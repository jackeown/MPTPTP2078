%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 159 expanded)
%              Number of leaves         :   20 (  76 expanded)
%              Depth                    :    6
%              Number of atoms          :  308 ( 554 expanded)
%              Number of equality atoms :   41 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f40,f56,f60,f64,f71,f94,f99,f113,f153,f172,f236,f255,f274,f296,f305])).

fof(f305,plain,
    ( ~ spl5_1
    | ~ spl5_8
    | ~ spl5_35
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_35
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f27,f273,f295,f55])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_8
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f295,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl5_37
  <=> ! [X1] : ~ r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f273,plain,
    ( r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl5_35
  <=> r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f27,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl5_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f296,plain,
    ( spl5_37
    | spl5_2
    | ~ spl5_10
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f283,f272,f62,f30,f294])).

fof(f30,plain,
    ( spl5_2
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f62,plain,
    ( spl5_10
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
        | ~ r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f283,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
    | spl5_2
    | ~ spl5_10
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f281,f31])).

fof(f31,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f281,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
        | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) )
    | ~ spl5_10
    | ~ spl5_35 ),
    inference(resolution,[],[f273,f63])).

fof(f63,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(sK1(X0,X1),X1)
        | ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
        | k2_relat_1(X0) = X1 )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f62])).

fof(f274,plain,
    ( spl5_35
    | spl5_2
    | ~ spl5_11
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f261,f253,f69,f30,f272])).

fof(f69,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0)
        | r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f253,plain,
    ( spl5_32
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f261,plain,
    ( r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | spl5_2
    | ~ spl5_11
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f260,f31])).

fof(f260,plain,
    ( r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl5_11
    | ~ spl5_32 ),
    inference(resolution,[],[f254,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0)
        | r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f254,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl5_32
    | ~ spl5_1
    | spl5_2
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f242,f234,f30,f26,f253])).

fof(f234,plain,
    ( spl5_30
  <=> ! [X13,X12] :
        ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(X12))
        | ~ r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(X12))),X13),X12)
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f241,f31])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)
        | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) )
    | ~ spl5_1
    | ~ spl5_30 ),
    inference(resolution,[],[f235,f27])).

fof(f235,plain,
    ( ! [X12,X13] :
        ( ~ v1_relat_1(X12)
        | ~ r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(X12))),X13),X12)
        | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(X12)) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f234])).

fof(f236,plain,
    ( spl5_30
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f186,f170,f38,f234])).

fof(f38,plain,
    ( spl5_4
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | r2_hidden(X0,k1_relat_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f170,plain,
    ( spl5_26
  <=> ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f186,plain,
    ( ! [X12,X13] :
        ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(X12))
        | ~ r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(X12))),X13),X12)
        | ~ v1_relat_1(X12) )
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(resolution,[],[f171,f39])).

fof(f39,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | ~ v1_relat_1(X2) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f171,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( spl5_26
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f154,f151,f111,f54,f26,f170])).

fof(f111,plain,
    ( spl5_18
  <=> ! [X3,X4] :
        ( k2_relat_1(sK0) = k9_relat_1(sK0,X3)
        | ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3)
        | ~ r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f151,plain,
    ( spl5_24
  <=> ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1)
        | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f154,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1) )
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f152,f125])).

fof(f125,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X2)),X2)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X2)
        | ~ r2_hidden(sK1(sK0,k9_relat_1(sK0,X2)),k9_relat_1(sK0,X3)) )
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f123,f27])).

fof(f123,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X2)),X2)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X2)
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(sK1(sK0,k9_relat_1(sK0,X2)),k9_relat_1(sK0,X3)) )
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(resolution,[],[f112,f55])).

fof(f112,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0)
        | ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X3) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f111])).

fof(f152,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1)
        | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1)) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( spl5_24
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f124,f111,f69,f151])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1)
        | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1)) )
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1)
        | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1))
        | k2_relat_1(sK0) = k9_relat_1(sK0,X1) )
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(resolution,[],[f112,f70])).

fof(f113,plain,
    ( spl5_18
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f104,f97,f69,f62,f111])).

fof(f97,plain,
    ( spl5_16
  <=> ! [X1,X3,X0,X2] :
        ( k2_relat_1(X1) = k9_relat_1(sK0,X0)
        | ~ r2_hidden(k4_tarski(X2,sK1(X1,k9_relat_1(sK0,X0))),sK0)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X0))),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f104,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK0) = k9_relat_1(sK0,X3)
        | ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3)
        | ~ r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0) )
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f103,f63])).

fof(f103,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK0) = k9_relat_1(sK0,X3)
        | ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3)
        | ~ r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0)
        | r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3)) )
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK0) = k9_relat_1(sK0,X3)
        | ~ r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3)
        | ~ r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0)
        | r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3))
        | k2_relat_1(sK0) = k9_relat_1(sK0,X3) )
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(resolution,[],[f98,f70])).

fof(f98,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X2,sK1(X1,k9_relat_1(sK0,X0))),sK0)
        | k2_relat_1(X1) = k9_relat_1(sK0,X0)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X0))),X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f95,f92,f26,f97])).

fof(f92,plain,
    ( spl5_15
  <=> ! [X9,X11,X8,X10,X12] :
        ( ~ r2_hidden(k4_tarski(X8,sK1(X9,k9_relat_1(X10,X11))),X9)
        | k9_relat_1(X10,X11) = k2_relat_1(X9)
        | ~ r2_hidden(k4_tarski(X12,sK1(X9,k9_relat_1(X10,X11))),X10)
        | ~ r2_hidden(X12,X11)
        | ~ v1_relat_1(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f95,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_relat_1(X1) = k9_relat_1(sK0,X0)
        | ~ r2_hidden(k4_tarski(X2,sK1(X1,k9_relat_1(sK0,X0))),sK0)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X0))),X1) )
    | ~ spl5_1
    | ~ spl5_15 ),
    inference(resolution,[],[f93,f27])).

fof(f93,plain,
    ( ! [X12,X10,X8,X11,X9] :
        ( ~ v1_relat_1(X10)
        | k9_relat_1(X10,X11) = k2_relat_1(X9)
        | ~ r2_hidden(k4_tarski(X12,sK1(X9,k9_relat_1(X10,X11))),X10)
        | ~ r2_hidden(X12,X11)
        | ~ r2_hidden(k4_tarski(X8,sK1(X9,k9_relat_1(X10,X11))),X9) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl5_15
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f67,f62,f58,f92])).

fof(f58,plain,
    ( spl5_9
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f67,plain,
    ( ! [X12,X10,X8,X11,X9] :
        ( ~ r2_hidden(k4_tarski(X8,sK1(X9,k9_relat_1(X10,X11))),X9)
        | k9_relat_1(X10,X11) = k2_relat_1(X9)
        | ~ r2_hidden(k4_tarski(X12,sK1(X9,k9_relat_1(X10,X11))),X10)
        | ~ r2_hidden(X12,X11)
        | ~ v1_relat_1(X10) )
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ r2_hidden(X3,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f71,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f14,f69])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f64,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f15,f62])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f21,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f56,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f32,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f11,f30])).

fof(f11,plain,(
    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f28,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f10,f26])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (13568)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (13568)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f28,f32,f40,f56,f60,f64,f71,f94,f99,f113,f153,f172,f236,f255,f274,f296,f305])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_8 | ~spl5_35 | ~spl5_37),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f301])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    $false | (~spl5_1 | ~spl5_8 | ~spl5_35 | ~spl5_37)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f27,f273,f295,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) ) | ~spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl5_8 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)) ) | ~spl5_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f294])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    spl5_37 <=> ! [X1] : ~r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | ~spl5_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f272])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl5_35 <=> r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    spl5_1 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    spl5_37 | spl5_2 | ~spl5_10 | ~spl5_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f283,f272,f62,f30,f294])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    spl5_2 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl5_10 <=> ! [X1,X3,X0] : (~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)) ) | (spl5_2 | ~spl5_10 | ~spl5_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f281,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f30])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))) ) | (~spl5_10 | ~spl5_35)),
% 0.21/0.49    inference(resolution,[],[f273,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | k2_relat_1(X0) = X1) ) | ~spl5_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    spl5_35 | spl5_2 | ~spl5_11 | ~spl5_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f261,f253,f69,f30,f272])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl5_11 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl5_32 <=> ! [X0] : ~r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | (spl5_2 | ~spl5_11 | ~spl5_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f260,f31])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl5_11 | ~spl5_32)),
% 0.21/0.49    inference(resolution,[],[f254,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) ) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)) ) | ~spl5_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl5_32 | ~spl5_1 | spl5_2 | ~spl5_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f242,f234,f30,f26,f253])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    spl5_30 <=> ! [X13,X12] : (k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(X12)) | ~r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(X12))),X13),X12) | ~v1_relat_1(X12))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)) ) | (~spl5_1 | spl5_2 | ~spl5_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f241,f31])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0) | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))) ) | (~spl5_1 | ~spl5_30)),
% 0.21/0.49    inference(resolution,[],[f235,f27])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ( ! [X12,X13] : (~v1_relat_1(X12) | ~r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(X12))),X13),X12) | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(X12))) ) | ~spl5_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f234])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    spl5_30 | ~spl5_4 | ~spl5_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f186,f170,f38,f234])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl5_4 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl5_26 <=> ! [X1] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1) | k2_relat_1(sK0) = k9_relat_1(sK0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    ( ! [X12,X13] : (k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(X12)) | ~r2_hidden(k4_tarski(sK3(sK0,k9_relat_1(sK0,k1_relat_1(X12))),X13),X12) | ~v1_relat_1(X12)) ) | (~spl5_4 | ~spl5_26)),
% 0.21/0.49    inference(resolution,[],[f171,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) ) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f38])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1) | k2_relat_1(sK0) = k9_relat_1(sK0,X1)) ) | ~spl5_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl5_26 | ~spl5_1 | ~spl5_8 | ~spl5_18 | ~spl5_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f154,f151,f111,f54,f26,f170])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    spl5_18 <=> ! [X3,X4] : (k2_relat_1(sK0) = k9_relat_1(sK0,X3) | ~r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl5_24 <=> ! [X1] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1) | k2_relat_1(sK0) = k9_relat_1(sK0,X1) | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1) | k2_relat_1(sK0) = k9_relat_1(sK0,X1)) ) | (~spl5_1 | ~spl5_8 | ~spl5_18 | ~spl5_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X2)),X2) | k2_relat_1(sK0) = k9_relat_1(sK0,X2) | ~r2_hidden(sK1(sK0,k9_relat_1(sK0,X2)),k9_relat_1(sK0,X3))) ) | (~spl5_1 | ~spl5_8 | ~spl5_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f27])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X2)),X2) | k2_relat_1(sK0) = k9_relat_1(sK0,X2) | ~v1_relat_1(sK0) | ~r2_hidden(sK1(sK0,k9_relat_1(sK0,X2)),k9_relat_1(sK0,X3))) ) | (~spl5_8 | ~spl5_18)),
% 0.21/0.49    inference(resolution,[],[f112,f55])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0) | ~r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3) | k2_relat_1(sK0) = k9_relat_1(sK0,X3)) ) | ~spl5_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f111])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1) | k2_relat_1(sK0) = k9_relat_1(sK0,X1) | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1))) ) | ~spl5_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f151])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl5_24 | ~spl5_11 | ~spl5_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f124,f111,f69,f151])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1) | k2_relat_1(sK0) = k9_relat_1(sK0,X1) | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1))) ) | (~spl5_11 | ~spl5_18)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(sK3(sK0,k9_relat_1(sK0,X1)),X1) | k2_relat_1(sK0) = k9_relat_1(sK0,X1) | r2_hidden(sK1(sK0,k9_relat_1(sK0,X1)),k9_relat_1(sK0,X1)) | k2_relat_1(sK0) = k9_relat_1(sK0,X1)) ) | (~spl5_11 | ~spl5_18)),
% 0.21/0.49    inference(resolution,[],[f112,f70])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl5_18 | ~spl5_10 | ~spl5_11 | ~spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f104,f97,f69,f62,f111])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl5_16 <=> ! [X1,X3,X0,X2] : (k2_relat_1(X1) = k9_relat_1(sK0,X0) | ~r2_hidden(k4_tarski(X2,sK1(X1,k9_relat_1(sK0,X0))),sK0) | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X0))),X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X4,X3] : (k2_relat_1(sK0) = k9_relat_1(sK0,X3) | ~r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0)) ) | (~spl5_10 | ~spl5_11 | ~spl5_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f63])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X4,X3] : (k2_relat_1(sK0) = k9_relat_1(sK0,X3) | ~r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0) | r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3))) ) | (~spl5_11 | ~spl5_16)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X4,X3] : (k2_relat_1(sK0) = k9_relat_1(sK0,X3) | ~r2_hidden(sK3(sK0,k9_relat_1(sK0,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0) | r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3)) | k2_relat_1(sK0) = k9_relat_1(sK0,X3)) ) | (~spl5_11 | ~spl5_16)),
% 0.21/0.49    inference(resolution,[],[f98,f70])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,sK1(X1,k9_relat_1(sK0,X0))),sK0) | k2_relat_1(X1) = k9_relat_1(sK0,X0) | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X0))),X1)) ) | ~spl5_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl5_16 | ~spl5_1 | ~spl5_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f95,f92,f26,f97])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl5_15 <=> ! [X9,X11,X8,X10,X12] : (~r2_hidden(k4_tarski(X8,sK1(X9,k9_relat_1(X10,X11))),X9) | k9_relat_1(X10,X11) = k2_relat_1(X9) | ~r2_hidden(k4_tarski(X12,sK1(X9,k9_relat_1(X10,X11))),X10) | ~r2_hidden(X12,X11) | ~v1_relat_1(X10))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_relat_1(X1) = k9_relat_1(sK0,X0) | ~r2_hidden(k4_tarski(X2,sK1(X1,k9_relat_1(sK0,X0))),sK0) | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X0))),X1)) ) | (~spl5_1 | ~spl5_15)),
% 0.21/0.49    inference(resolution,[],[f93,f27])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X12,X10,X8,X11,X9] : (~v1_relat_1(X10) | k9_relat_1(X10,X11) = k2_relat_1(X9) | ~r2_hidden(k4_tarski(X12,sK1(X9,k9_relat_1(X10,X11))),X10) | ~r2_hidden(X12,X11) | ~r2_hidden(k4_tarski(X8,sK1(X9,k9_relat_1(X10,X11))),X9)) ) | ~spl5_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl5_15 | ~spl5_9 | ~spl5_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f67,f62,f58,f92])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl5_9 <=> ! [X1,X3,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X12,X10,X8,X11,X9] : (~r2_hidden(k4_tarski(X8,sK1(X9,k9_relat_1(X10,X11))),X9) | k9_relat_1(X10,X11) = k2_relat_1(X9) | ~r2_hidden(k4_tarski(X12,sK1(X9,k9_relat_1(X10,X11))),X10) | ~r2_hidden(X12,X11) | ~v1_relat_1(X10)) ) | (~spl5_9 | ~spl5_10)),
% 0.21/0.49    inference(resolution,[],[f63,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | ~v1_relat_1(X2)) ) | ~spl5_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl5_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f69])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl5_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f62])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl5_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f21,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl5_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f54])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f38])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f11,f30])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f10,f26])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13568)------------------------------
% 0.21/0.49  % (13568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13568)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13568)Memory used [KB]: 10874
% 0.21/0.49  % (13568)Time elapsed: 0.038 s
% 0.21/0.49  % (13568)------------------------------
% 0.21/0.49  % (13568)------------------------------
% 0.21/0.49  % (13554)Success in time 0.134 s
%------------------------------------------------------------------------------
