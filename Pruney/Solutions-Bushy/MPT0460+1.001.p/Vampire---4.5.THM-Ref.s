%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0460+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:01 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 272 expanded)
%              Number of leaves         :   32 ( 125 expanded)
%              Depth                    :    7
%              Number of atoms          :  595 (1092 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f724,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f49,f53,f57,f61,f65,f72,f76,f81,f85,f89,f94,f102,f106,f111,f117,f137,f143,f158,f178,f196,f219,f653,f677,f701,f723])).

fof(f723,plain,
    ( ~ spl9_16
    | spl9_5
    | ~ spl9_7
    | spl9_90 ),
    inference(avatar_split_clause,[],[f711,f699,f55,f47,f97])).

fof(f97,plain,
    ( spl9_16
  <=> v1_relat_1(k5_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f47,plain,
    ( spl9_5
  <=> r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f55,plain,
    ( spl9_7
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f699,plain,
    ( spl9_90
  <=> r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f711,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK0))
    | spl9_5
    | ~ spl9_7
    | spl9_90 ),
    inference(subsumption_resolution,[],[f707,f48])).

fof(f48,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f707,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK0))
    | r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))
    | ~ spl9_7
    | spl9_90 ),
    inference(resolution,[],[f700,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f700,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK0))
    | spl9_90 ),
    inference(avatar_component_clause,[],[f699])).

fof(f701,plain,
    ( ~ spl9_90
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_12
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f688,f675,f79,f39,f31,f699])).

fof(f31,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f39,plain,
    ( spl9_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f79,plain,
    ( spl9_12
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f675,plain,
    ( spl9_88
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f688,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK0))
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_12
    | ~ spl9_88 ),
    inference(subsumption_resolution,[],[f687,f32])).

fof(f32,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f687,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl9_3
    | ~ spl9_12
    | ~ spl9_88 ),
    inference(subsumption_resolution,[],[f686,f40])).

fof(f40,plain,
    ( v1_relat_1(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f686,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl9_12
    | ~ spl9_88 ),
    inference(duplicate_literal_removal,[],[f684])).

fof(f684,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK0))
    | ~ spl9_12
    | ~ spl9_88 ),
    inference(resolution,[],[f676,f80])).

fof(f80,plain,
    ( ! [X4,X0,X3,X1] :
        ( r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f676,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) )
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f675])).

fof(f677,plain,
    ( spl9_88
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f663,f651,f43,f39,f675])).

fof(f43,plain,
    ( spl9_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f651,plain,
    ( spl9_85
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f663,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_85 ),
    inference(subsumption_resolution,[],[f658,f40])).

fof(f658,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) )
    | ~ spl9_4
    | ~ spl9_85 ),
    inference(resolution,[],[f652,f44])).

fof(f44,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f652,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X2)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) )
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f651])).

fof(f653,plain,
    ( spl9_85
    | ~ spl9_1
    | ~ spl9_15
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f232,f217,f92,f31,f651])).

fof(f92,plain,
    ( spl9_15
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f217,plain,
    ( spl9_33
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) )
    | ~ spl9_1
    | ~ spl9_15
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f230,f32])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK2,X0,sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X1),k5_relat_1(sK2,X0)) )
    | ~ spl9_15
    | ~ spl9_33 ),
    inference(resolution,[],[f218,f93])).

fof(f93,plain,
    ( ! [X4,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f92])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl9_33
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f211,f194,f70,f31,f217])).

fof(f70,plain,
    ( spl9_10
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f194,plain,
    ( spl9_30
  <=> ! [X3,X5,X4] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X3),X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,sK2)
        | ~ r2_hidden(k4_tarski(X3,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f210,f32])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl9_10
    | ~ spl9_30 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_10
    | ~ spl9_30 ),
    inference(resolution,[],[f195,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( r1_tarski(X0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f195,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X4,sK2)
        | ~ v1_relat_1(X4)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X3),X4)
        | ~ r2_hidden(k4_tarski(X3,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,sK1) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( spl9_30
    | ~ spl9_9
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f187,f176,f63,f194])).

fof(f63,plain,
    ( spl9_9
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(k4_tarski(X2,X3),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f176,plain,
    ( spl9_28
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_tarski(X2,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X2),X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f187,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X3),X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,sK2)
        | ~ r2_hidden(k4_tarski(X3,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,sK1) )
    | ~ spl9_9
    | ~ spl9_28 ),
    inference(resolution,[],[f177,f64])).

fof(f64,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X2,X3),X1)
        | ~ r2_hidden(k4_tarski(X2,X3),X0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f177,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X2),X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl9_28
    | ~ spl9_9
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f169,f156,f63,f176])).

fof(f156,plain,
    ( spl9_25
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f169,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X2),X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl9_9
    | ~ spl9_25 ),
    inference(resolution,[],[f157,f64])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1) )
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl9_25
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_19
    | spl9_23 ),
    inference(avatar_split_clause,[],[f151,f135,f109,f35,f31,f156])).

fof(f35,plain,
    ( spl9_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f109,plain,
    ( spl9_19
  <=> ! [X1,X3,X5,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f135,plain,
    ( spl9_23
  <=> r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_19
    | spl9_23 ),
    inference(subsumption_resolution,[],[f150,f32])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_2
    | ~ spl9_19
    | spl9_23 ),
    inference(subsumption_resolution,[],[f148,f36])).

fof(f36,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_19
    | spl9_23 ),
    inference(resolution,[],[f136,f110])).

fof(f110,plain,
    ( ! [X4,X0,X5,X3,X1] :
        ( r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f109])).

fof(f136,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK1))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f135])).

fof(f143,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | spl9_22 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | spl9_22 ),
    inference(subsumption_resolution,[],[f141,f32])).

fof(f141,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_6
    | spl9_22 ),
    inference(subsumption_resolution,[],[f139,f36])).

fof(f139,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_6
    | spl9_22 ),
    inference(resolution,[],[f133,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl9_6
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f133,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | spl9_22 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_22
  <=> v1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f137,plain,
    ( ~ spl9_22
    | ~ spl9_23
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f122,f100,f70,f135,f132])).

fof(f100,plain,
    ( spl9_17
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X0)
        | ~ r1_tarski(X0,k5_relat_1(sK2,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f122,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(resolution,[],[f101,f71])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_relat_1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f100])).

fof(f117,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_6
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_6
    | spl9_16 ),
    inference(subsumption_resolution,[],[f115,f32])).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_3
    | ~ spl9_6
    | spl9_16 ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f113,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl9_6
    | spl9_16 ),
    inference(resolution,[],[f98,f52])).

fof(f98,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK0))
    | spl9_16 ),
    inference(avatar_component_clause,[],[f97])).

fof(f111,plain,
    ( spl9_19
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f107,f104,f51,f109])).

fof(f104,plain,
    ( spl9_18
  <=> ! [X1,X3,X5,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f107,plain,
    ( ! [X4,X0,X5,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f105,f52])).

fof(f105,plain,
    ( ! [X4,X0,X5,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f27,f104])).

fof(f27,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f102,plain,
    ( ~ spl9_16
    | spl9_17
    | spl9_5
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f95,f83,f47,f100,f97])).

fof(f83,plain,
    ( spl9_13
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k5_relat_1(sK2,sK1))
        | ~ v1_relat_1(k5_relat_1(sK2,sK0))
        | ~ r2_hidden(k4_tarski(sK7(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)),sK8(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),X0) )
    | spl9_5
    | ~ spl9_13 ),
    inference(resolution,[],[f84,f48])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X2) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f94,plain,
    ( spl9_15
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f90,f87,f51,f92])).

fof(f87,plain,
    ( spl9_14
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f90,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f88,f52])).

fof(f88,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f29,f87])).

fof(f29,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,
    ( spl9_13
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f68,f63,f59,f83])).

fof(f59,plain,
    ( spl9_8
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) )
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(resolution,[],[f64,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f81,plain,
    ( spl9_12
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f77,f74,f51,f79])).

fof(f74,plain,
    ( spl9_11
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f77,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f75,f52])).

fof(f75,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,
    ( spl9_10
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f67,f59,f55,f70])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,X0) )
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X0) )
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(resolution,[],[f60,f56])).

fof(f65,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f61,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f49,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f14,f47])).

fof(f14,plain,(
    ~ r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( r1_tarski(X0,X1)
                 => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f45,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f13,f43])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f12,f31])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
