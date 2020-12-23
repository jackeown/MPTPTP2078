%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0782+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:39 EST 2020

% Result     : Theorem 7.65s
% Output     : Refutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 338 expanded)
%              Number of leaves         :   49 ( 159 expanded)
%              Depth                    :    7
%              Number of atoms          :  812 (1357 expanded)
%              Number of equality atoms :   66 ( 112 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6627,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f76,f80,f84,f92,f96,f100,f104,f108,f112,f116,f121,f125,f129,f133,f137,f143,f149,f168,f183,f197,f213,f395,f820,f1339,f2797,f4129,f6484,f6499,f6515,f6546,f6565,f6579,f6597,f6626])).

fof(f6626,plain,
    ( spl5_3
    | ~ spl5_1013 ),
    inference(avatar_contradiction_clause,[],[f6600])).

fof(f6600,plain,
    ( $false
    | spl5_3
    | ~ spl5_1013 ),
    inference(unit_resulting_resolution,[],[f59,f6596])).

fof(f6596,plain,
    ( ! [X0] : v1_wellord1(k2_wellord1(sK1,X0))
    | ~ spl5_1013 ),
    inference(avatar_component_clause,[],[f6595])).

fof(f6595,plain,
    ( spl5_1013
  <=> ! [X0] : v1_wellord1(k2_wellord1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1013])])).

fof(f59,plain,
    ( ~ v1_wellord1(k2_wellord1(sK1,sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_3
  <=> v1_wellord1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f6597,plain,
    ( spl5_1013
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_1010 ),
    inference(avatar_split_clause,[],[f6588,f6577,f102,f50,f6595])).

fof(f50,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f102,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f6577,plain,
    ( spl5_1010
  <=> ! [X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),k3_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1010])])).

fof(f6588,plain,
    ( ! [X0] : v1_wellord1(k2_wellord1(sK1,X0))
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_1010 ),
    inference(subsumption_resolution,[],[f6584,f51])).

fof(f51,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f6584,plain,
    ( ! [X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_14
    | ~ spl5_1010 ),
    inference(resolution,[],[f6578,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f6578,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_1010 ),
    inference(avatar_component_clause,[],[f6577])).

fof(f6579,plain,
    ( spl5_1010
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_1008 ),
    inference(avatar_split_clause,[],[f6569,f6563,f62,f50,f6577])).

fof(f62,plain,
    ( spl5_4
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f6563,plain,
    ( spl5_1008
  <=> ! [X5] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X5)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X5))
        | ~ v1_relat_1(k2_wellord1(sK1,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1008])])).

fof(f6569,plain,
    ( ! [X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),k3_relat_1(sK1)) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_1008 ),
    inference(subsumption_resolution,[],[f6568,f51])).

fof(f6568,plain,
    ( ! [X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_4
    | ~ spl5_1008 ),
    inference(resolution,[],[f6564,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k2_wellord1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f6564,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(k2_wellord1(sK1,X5))
        | v1_wellord1(k2_wellord1(sK1,X5))
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X5)),k3_relat_1(sK1)) )
    | ~ spl5_1008 ),
    inference(avatar_component_clause,[],[f6563])).

fof(f6565,plain,
    ( spl5_1008
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_1005 ),
    inference(avatar_split_clause,[],[f6555,f6544,f94,f74,f6563])).

fof(f74,plain,
    ( spl5_7
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != sK2(X0)
        | v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f94,plain,
    ( spl5_12
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(sK2(X0),k3_relat_1(X0))
        | v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f6544,plain,
    ( spl5_1005
  <=> ! [X1,X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1005])])).

fof(f6555,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X5)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X5))
        | ~ v1_relat_1(k2_wellord1(sK1,X5)) )
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_1005 ),
    inference(subsumption_resolution,[],[f6554,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( k1_xboole_0 != sK2(X0)
        | ~ v1_relat_1(X0)
        | v1_wellord1(X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f6554,plain,
    ( ! [X5] :
        ( k1_xboole_0 = sK2(k2_wellord1(sK1,X5))
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X5)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X5))
        | ~ v1_relat_1(k2_wellord1(sK1,X5)) )
    | ~ spl5_12
    | ~ spl5_1005 ),
    inference(duplicate_literal_removal,[],[f6553])).

fof(f6553,plain,
    ( ! [X5] :
        ( k1_xboole_0 = sK2(k2_wellord1(sK1,X5))
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,X5)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X5))
        | ~ v1_relat_1(k2_wellord1(sK1,X5))
        | v1_wellord1(k2_wellord1(sK1,X5)) )
    | ~ spl5_12
    | ~ spl5_1005 ),
    inference(resolution,[],[f6545,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(X0),k3_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_wellord1(X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f6545,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),X1)
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_1005 ),
    inference(avatar_component_clause,[],[f6544])).

fof(f6546,plain,
    ( spl5_1005
    | ~ spl5_15
    | ~ spl5_1000 ),
    inference(avatar_split_clause,[],[f6520,f6513,f106,f6544])).

fof(f106,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f6513,plain,
    ( spl5_1000
  <=> ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1000])])).

fof(f6520,plain,
    ( ! [X0,X1] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),X1) )
    | ~ spl5_15
    | ~ spl5_1000 ),
    inference(resolution,[],[f6514,f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f6514,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0)) )
    | ~ spl5_1000 ),
    inference(avatar_component_clause,[],[f6513])).

fof(f6515,plain,
    ( spl5_1000
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_21
    | ~ spl5_998 ),
    inference(avatar_split_clause,[],[f6505,f6497,f131,f54,f50,f6513])).

fof(f54,plain,
    ( spl5_2
  <=> v1_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f131,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | r2_hidden(sK3(X0,X1),X1)
        | ~ v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f6497,plain,
    ( spl5_998
  <=> ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | v1_wellord1(k2_wellord1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_998])])).

fof(f6505,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_21
    | ~ spl5_998 ),
    inference(subsumption_resolution,[],[f6504,f55])).

fof(f55,plain,
    ( v1_wellord1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f6504,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ v1_wellord1(sK1) )
    | ~ spl5_1
    | ~ spl5_21
    | ~ spl5_998 ),
    inference(subsumption_resolution,[],[f6503,f51])).

fof(f6503,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_wellord1(sK1) )
    | ~ spl5_21
    | ~ spl5_998 ),
    inference(duplicate_literal_removal,[],[f6501])).

fof(f6501,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_wellord1(sK1) )
    | ~ spl5_21
    | ~ spl5_998 ),
    inference(resolution,[],[f6498,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X1)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | ~ v1_relat_1(X0)
        | ~ v1_wellord1(X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f131])).

fof(f6498,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_998 ),
    inference(avatar_component_clause,[],[f6497])).

fof(f6499,plain,
    ( spl5_998
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_995 ),
    inference(avatar_split_clause,[],[f6490,f6482,f62,f50,f6497])).

fof(f6482,plain,
    ( spl5_995
  <=> ! [X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ v1_relat_1(k2_wellord1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_995])])).

fof(f6490,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_995 ),
    inference(subsumption_resolution,[],[f6489,f51])).

fof(f6489,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_4
    | ~ spl5_995 ),
    inference(resolution,[],[f6483,f63])).

fof(f6483,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_995 ),
    inference(avatar_component_clause,[],[f6482])).

fof(f6484,plain,
    ( spl5_995
    | ~ spl5_7
    | ~ spl5_19
    | ~ spl5_630 ),
    inference(avatar_split_clause,[],[f4137,f4127,f123,f74,f6482])).

fof(f123,plain,
    ( spl5_19
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,sK2(X0))
        | ~ r1_xboole_0(k1_wellord1(X0,X2),sK2(X0))
        | v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f4127,plain,
    ( spl5_630
  <=> ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_630])])).

fof(f4137,plain,
    ( ! [X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ v1_relat_1(k2_wellord1(sK1,X0)) )
    | ~ spl5_7
    | ~ spl5_19
    | ~ spl5_630 ),
    inference(subsumption_resolution,[],[f4136,f75])).

fof(f4136,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ v1_relat_1(k2_wellord1(sK1,X0)) )
    | ~ spl5_19
    | ~ spl5_630 ),
    inference(duplicate_literal_removal,[],[f4134])).

fof(f4134,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ v1_relat_1(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_19
    | ~ spl5_630 ),
    inference(resolution,[],[f4128,f124])).

fof(f124,plain,
    ( ! [X2,X0] :
        ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK2(X0))
        | ~ r2_hidden(X2,sK2(X0))
        | ~ v1_relat_1(X0)
        | v1_wellord1(X0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f4128,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1)) )
    | ~ spl5_630 ),
    inference(avatar_component_clause,[],[f4127])).

fof(f4129,plain,
    ( spl5_630
    | ~ spl5_9
    | ~ spl5_428 ),
    inference(avatar_split_clause,[],[f2802,f2795,f82,f4127])).

fof(f82,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK4(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f2795,plain,
    ( spl5_428
  <=> ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_428])])).

fof(f2802,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))) )
    | ~ spl5_9
    | ~ spl5_428 ),
    inference(resolution,[],[f2796,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f2796,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_428 ),
    inference(avatar_component_clause,[],[f2795])).

fof(f2797,plain,
    ( spl5_428
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_21
    | ~ spl5_206 ),
    inference(avatar_split_clause,[],[f1348,f1337,f131,f54,f50,f2795])).

fof(f1337,plain,
    ( spl5_206
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,X1)),sK2(k2_wellord1(sK1,X0))),X1)
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,X1),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = X1
        | v1_wellord1(k2_wellord1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f1348,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_21
    | ~ spl5_206 ),
    inference(subsumption_resolution,[],[f1347,f55])).

fof(f1347,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ v1_wellord1(sK1) )
    | ~ spl5_1
    | ~ spl5_21
    | ~ spl5_206 ),
    inference(subsumption_resolution,[],[f1346,f51])).

fof(f1346,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_wellord1(sK1) )
    | ~ spl5_21
    | ~ spl5_206 ),
    inference(duplicate_literal_removal,[],[f1344])).

fof(f1344,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,sK2(k2_wellord1(sK1,X0)))),sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_wellord1(sK1) )
    | ~ spl5_21
    | ~ spl5_206 ),
    inference(resolution,[],[f1338,f132])).

fof(f1338,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK1,X1),sK2(k2_wellord1(sK1,X0)))
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,X1)),sK2(k2_wellord1(sK1,X0))),X1)
        | k1_xboole_0 = X1
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_206 ),
    inference(avatar_component_clause,[],[f1337])).

fof(f1339,plain,
    ( spl5_206
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f826,f818,f62,f50,f1337])).

fof(f818,plain,
    ( spl5_126
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),sK2(k2_wellord1(sK1,X1))),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,X0),sK2(k2_wellord1(sK1,X1)))
        | ~ v1_relat_1(k2_wellord1(sK1,X1))
        | v1_wellord1(k2_wellord1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f826,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,X1)),sK2(k2_wellord1(sK1,X0))),X1)
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,X1),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = X1
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_126 ),
    inference(subsumption_resolution,[],[f825,f51])).

fof(f825,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X0),sK3(sK1,X1)),sK2(k2_wellord1(sK1,X0))),X1)
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,X1),sK2(k2_wellord1(sK1,X0)))
        | k1_xboole_0 = X1
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_4
    | ~ spl5_126 ),
    inference(resolution,[],[f819,f63])).

fof(f819,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k2_wellord1(sK1,X1))
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),sK2(k2_wellord1(sK1,X1))),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,X0),sK2(k2_wellord1(sK1,X1)))
        | k1_xboole_0 = X0
        | v1_wellord1(k2_wellord1(sK1,X1)) )
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f818])).

fof(f820,plain,
    ( spl5_126
    | ~ spl5_19
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f396,f393,f123,f818])).

fof(f393,plain,
    ( spl5_61
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X2),X0)
        | r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f396,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),sK2(k2_wellord1(sK1,X1))),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,X0),sK2(k2_wellord1(sK1,X1)))
        | ~ v1_relat_1(k2_wellord1(sK1,X1))
        | v1_wellord1(k2_wellord1(sK1,X1)) )
    | ~ spl5_19
    | ~ spl5_61 ),
    inference(resolution,[],[f394,f124])).

fof(f394,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X2)
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X2),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK1)) )
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f393])).

fof(f395,plain,
    ( spl5_61
    | ~ spl5_8
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f218,f211,f78,f393])).

fof(f78,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK4(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f211,plain,
    ( spl5_34
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,k1_wellord1(k2_wellord1(sK1,X2),sK3(sK1,X0)))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f218,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK4(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X2),X0)
        | r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X2) )
    | ~ spl5_8
    | ~ spl5_34 ),
    inference(resolution,[],[f212,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k1_wellord1(k2_wellord1(sK1,X2),sK3(sK1,X0)))
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl5_34
    | ~ spl5_1
    | ~ spl5_18
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f204,f195,f119,f50,f211])).

fof(f119,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f195,plain,
    ( spl5_32
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X2,k1_wellord1(sK1,sK3(sK1,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,k1_wellord1(k2_wellord1(sK1,X2),sK3(sK1,X0)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_1
    | ~ spl5_18
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f200,f51])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,k1_wellord1(k2_wellord1(sK1,X2),sK3(sK1,X0)))
        | ~ r2_hidden(X1,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_18
    | ~ spl5_32 ),
    inference(resolution,[],[f196,f120])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,k1_wellord1(sK1,sK3(sK1,X1)))
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( spl5_32
    | ~ spl5_5
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f186,f181,f66,f195])).

fof(f66,plain,
    ( spl5_5
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f181,plain,
    ( spl5_30
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 = X2
        | ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X2,k1_wellord1(sK1,sK3(sK1,X1))) )
    | ~ spl5_5
    | ~ spl5_30 ),
    inference(resolution,[],[f182,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X2))))
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 = X2
        | ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f181])).

fof(f183,plain,
    ( spl5_30
    | ~ spl5_17
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f175,f166,f114,f181])).

fof(f114,plain,
    ( spl5_17
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f166,plain,
    ( spl5_27
  <=> ! [X9,X7,X8,X6] :
        ( ~ r1_tarski(X6,k3_relat_1(sK1))
        | ~ r2_hidden(X7,X6)
        | k1_xboole_0 = X6
        | ~ r2_hidden(X8,X9)
        | ~ m1_subset_1(X7,k1_wellord1(sK1,sK3(sK1,X6)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 = X2
        | ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X2)))) )
    | ~ spl5_17
    | ~ spl5_27 ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 = X2
        | ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X2))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X2)))) )
    | ~ spl5_17
    | ~ spl5_27 ),
    inference(condensation,[],[f173])).

fof(f173,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,X3)
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X1))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X1))))
        | ~ r2_hidden(X0,X4) )
    | ~ spl5_17
    | ~ spl5_27 ),
    inference(resolution,[],[f167,f115])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f167,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ m1_subset_1(X7,k1_wellord1(sK1,sK3(sK1,X6)))
        | ~ r2_hidden(X7,X6)
        | k1_xboole_0 = X6
        | ~ r2_hidden(X8,X9)
        | ~ r1_tarski(X6,k3_relat_1(sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X6)))) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl5_27
    | ~ spl5_20
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f153,f147,f127,f166])).

fof(f127,plain,
    ( spl5_20
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f147,plain,
    ( spl5_24
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,k1_wellord1(sK1,sK3(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f153,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ r1_tarski(X6,k3_relat_1(sK1))
        | ~ r2_hidden(X7,X6)
        | k1_xboole_0 = X6
        | ~ r2_hidden(X8,X9)
        | ~ m1_subset_1(X7,k1_wellord1(sK1,sK3(sK1,X6)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X6)))) )
    | ~ spl5_20
    | ~ spl5_24 ),
    inference(resolution,[],[f148,f128])).

fof(f128,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_wellord1(sK1,sK3(sK1,X0)))
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl5_24
    | ~ spl5_13
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f145,f141,f98,f147])).

fof(f98,plain,
    ( spl5_13
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f141,plain,
    ( spl5_23
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK1,sK3(sK1,X0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,k1_wellord1(sK1,sK3(sK1,X0))) )
    | ~ spl5_13
    | ~ spl5_23 ),
    inference(resolution,[],[f142,f99])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f142,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_wellord1(sK1,sK3(sK1,X0)),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1)) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl5_23
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f139,f135,f54,f50,f141])).

fof(f135,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | r1_xboole_0(k1_wellord1(X0,sK3(X0,X1)),X1)
        | ~ v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK1,sK3(sK1,X0)),X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f138,f51])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK1,sK3(sK1,X0)),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(resolution,[],[f136,f55])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ v1_wellord1(X0)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | r1_xboole_0(k1_wellord1(X0,sK3(X0,X1)),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f33,f135])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r1_xboole_0(k1_wellord1(X0,sK3(X0,X1)),X1)
      | ~ v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_wellord1)).

fof(f133,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f32,f131])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f129,plain,
    ( spl5_20
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f117,f110,f90,f127])).

fof(f90,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f110,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f117,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) )
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(resolution,[],[f111,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f125,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f31,f123])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,sK2(X0))
      | ~ r1_xboole_0(k1_wellord1(X0,X2),sK2(X0))
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f45,f119])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_wellord1)).

fof(f116,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f46,f114])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f112,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f48,f110])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f108,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f104,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f40,f102])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(f100,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f96,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f34,f94])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(sK2(X0),k3_relat_1(X0))
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f84,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != sK2(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f43,f66])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f39,f62])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f60,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f30,f58])).

fof(f30,plain,(
    ~ v1_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ v1_wellord1(k2_wellord1(X1,X0))
      & v1_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ v1_wellord1(k2_wellord1(X1,X0))
      & v1_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v1_wellord1(X1)
         => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord1)).

fof(f56,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    v1_wellord1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
