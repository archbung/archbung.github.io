{-# LANGUAGE OverloadedStrings #-}

import           Hakyll
import           Text.Pandoc.Options

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------
config :: Configuration
config =
  defaultConfiguration
    { destinationDirectory = "docs"
    }

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------
main :: IO ()
main = hakyllWith config $ do
    -- Static files
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "CNAME" $ do
        route   idRoute
        compile copyFileCompiler

    -- Tags
    tags <- buildTags "posts/*" (fromCapture "tags/*.html")

    -- Render tags pages
    tagsRules tags $ \tag pattern -> do
        let title = "Posts tagged \"" ++ tag ++ "\""
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll pattern
            let ctx = constField "title" title
                      `mappend` listField "posts" postCtx (return posts)  -- Use simple postCtx
                      `mappend` defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/tag.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    -- About and contact pages
    match (fromList ["about.md", "about.org", "contact.md", "contact.org"]) $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    -- Blog posts - Let pandoc handle everything
    match "posts/*" $ version "full" $ do
        route $ setExtension "html"
        compile $ do
            let postCtxWithTags = postCtxWith tags
            pandocCompilerWith defaultHakyllReaderOptions defaultHakyllWriterOptions
                >>= saveSnapshot "content"
                >>= loadAndApplyTemplate "templates/post.html"    postCtxWithTags
                >>= loadAndApplyTemplate "templates/default.html" postCtxWithTags
                >>= relativizeUrls

    -- Archive
    create ["archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll ("posts/*" .&&. hasVersion "full")
            let archiveCtx =
                    listField "posts" postCtx (return posts)  -- Use simple postCtx
                    `mappend` constField "title" "Archives"
                    `mappend` defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

    -- Index
    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- fmap (take 5) . recentFirst =<<
                     loadAll ("posts/*" .&&. hasVersion "full")
            let indexCtx =
                    listField "posts" postCtx (return posts)  -- Use simple postCtx
                    `mappend` constField "home" "true"
                    `mappend` defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    -- Templates
    match "templates/*" $ compile templateBodyCompiler

    -- RSS feed
    create ["rss.xml"] $ do
        route idRoute
        compile $ do
            posts <- fmap (take 10) . recentFirst =<<
                     loadAllSnapshots ("posts/*" .&&. hasVersion "full") "content"
            renderRss feedConfiguration feedContext posts

    -- Sitemap
    create ["sitemap.xml"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll ("posts/*" .&&. hasVersion "full")
            pages <- loadAll (fromList ["about.html", "contact.html", "archive.html"])
            let allPages = pages ++ posts
                sitemapCtx = listField "pages" postCtx (return allPages)
            makeItem ""
                >>= loadAndApplyTemplate "templates/sitemap.xml" sitemapCtx

--------------------------------------------------------------------------------
-- Contexts
--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    titleField "title"  -- Explicitly add title field
    `mappend` dateField "date" "%B %e, %Y"
    `mappend` defaultContext

postCtxWithReadingTime :: Context String
postCtxWithReadingTime =
    dateField "date" "%B %e, %Y"
    `mappend` readingTimeField "readingtime"
    `mappend` defaultContext

postCtxWith :: Tags -> Context String
postCtxWith tags =
    tagsField "tags" tags
    `mappend` postCtxWithReadingTime

feedContext :: Context String
feedContext =
    postCtx
    `mappend` bodyField "description"

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------
readingTimeField :: String -> Context String
readingTimeField key = field key $ \item -> do
    body <- loadSnapshot (itemIdentifier item) "content"
    let wordCount = length (words $ itemBody body)
        readingTime = max 1 $ wordCount `div` 200
    return $ show readingTime ++ " min read"

--------------------------------------------------------------------------------
-- Feed configuration
--------------------------------------------------------------------------------
feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
    { feedTitle       = "archbung :: Blog"
    , feedDescription = "Functional Programming & Software Engineering"
    , feedAuthorName  = "archbung"
    , feedAuthorEmail = "your-email@example.com"
    , feedRoot        = "https://archbung.github.io"
    }
