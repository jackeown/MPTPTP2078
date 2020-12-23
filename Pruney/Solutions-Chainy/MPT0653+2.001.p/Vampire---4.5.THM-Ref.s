%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  256 ( 642 expanded)
%              Number of leaves         :   41 ( 275 expanded)
%              Depth                    :   16
%              Number of atoms          : 1496 (3301 expanded)
%              Number of equality atoms :  313 ( 852 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f876,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f125,f141,f220,f233,f241,f268,f287,f305,f320,f324,f344,f348,f364,f375,f385,f415,f419,f436,f446,f470,f474,f564,f588,f652,f702,f823,f836,f875])).

fof(f875,plain,
    ( spl7_37
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f826,f650,f562,f315])).

fof(f315,plain,
    ( spl7_37
  <=> r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f562,plain,
    ( spl7_54
  <=> sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f650,plain,
    ( spl7_58
  <=> r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f826,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f651,f563])).

fof(f563,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f562])).

fof(f651,plain,
    ( r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k2_relat_1(sK0))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f650])).

fof(f836,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_38
    | ~ spl7_41
    | ~ spl7_54 ),
    inference(avatar_contradiction_clause,[],[f835])).

fof(f835,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_38
    | ~ spl7_41
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f834,f824])).

fof(f824,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_41
    | ~ spl7_54 ),
    inference(backward_demodulation,[],[f347,f563])).

fof(f347,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl7_41
  <=> sK3(sK0,sK1) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f834,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_38
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f829,f319])).

fof(f319,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl7_38
  <=> r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f829,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_54 ),
    inference(trivial_inequality_removal,[],[f825])).

fof(f825,plain,
    ( sK2(sK0,sK1) != sK2(sK0,sK1)
    | ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_54 ),
    inference(backward_demodulation,[],[f533,f563])).

fof(f533,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f532,f82])).

fof(f82,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_7
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f532,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f531,f78])).

fof(f78,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_6
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f531,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f530,f70])).

fof(f70,plain,
    ( v1_relat_1(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f530,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f529,f86])).

fof(f86,plain,
    ( k1_relat_1(sK1) = k2_relat_1(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_8
  <=> k1_relat_1(sK1) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f529,plain,
    ( k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f528,f62])).

fof(f62,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f528,plain,
    ( ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f527,f58])).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f527,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f526,f66])).

fof(f66,plain,
    ( v2_funct_1(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f526,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_5
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f519,f74])).

fof(f74,plain,
    ( v1_funct_1(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f519,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_34
    | ~ spl7_37 ),
    inference(resolution,[],[f316,f286])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
        | ~ v1_relat_1(X0)
        | sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        | k2_funct_1(X0) = X1 )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl7_34
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
        | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0))
        | sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        | k2_funct_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f316,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f315])).

fof(f823,plain,
    ( spl7_54
    | spl7_55
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f369,f362,f85,f77,f61,f57,f586,f562])).

fof(f586,plain,
    ( spl7_55
  <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f362,plain,
    ( spl7_42
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f369,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f368,f78])).

fof(f368,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f367,f86])).

fof(f367,plain,
    ( k1_relat_1(sK1) != k2_relat_1(sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f365,f58])).

fof(f365,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_2
    | ~ spl7_42 ),
    inference(resolution,[],[f363,f62])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f362])).

fof(f702,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_51
    | ~ spl7_55 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_51
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f700,f653])).

fof(f653,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl7_46
    | ~ spl7_55 ),
    inference(backward_demodulation,[],[f418,f587])).

fof(f587,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f586])).

fof(f418,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl7_46
  <=> sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f700,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_51
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f660,f659])).

fof(f659,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_51
    | ~ spl7_55 ),
    inference(backward_demodulation,[],[f576,f587])).

fof(f576,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k2_relat_1(sK1))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_51 ),
    inference(backward_demodulation,[],[f473,f574])).

fof(f574,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK0,sK2(sK0,sK1))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_51 ),
    inference(forward_demodulation,[],[f568,f539])).

fof(f539,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK5(sK0,sK2(sK0,sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f457,f537])).

fof(f537,plain,
    ( sK2(sK0,sK1) = sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1)))
    | ~ spl7_17
    | ~ spl7_37
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f535,f418])).

fof(f535,plain,
    ( k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) = sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1)))
    | ~ spl7_17
    | ~ spl7_37
    | ~ spl7_48
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f453,f520])).

fof(f520,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))))
    | ~ spl7_37
    | ~ spl7_50 ),
    inference(resolution,[],[f316,f469])).

fof(f469,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0))) )
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl7_50
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f453,plain,
    ( sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1)))))
    | ~ spl7_17
    | ~ spl7_48 ),
    inference(resolution,[],[f445,f140])).

fof(f140,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1 )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_17
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f445,plain,
    ( r2_hidden(sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))),k2_relat_1(sK0))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl7_48
  <=> r2_hidden(sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f457,plain,
    ( sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,sK5(sK0,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1)))))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f456,f70])).

fof(f456,plain,
    ( sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,sK5(sK0,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1)))))
    | ~ v1_relat_1(sK0)
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f454,f74])).

fof(f454,plain,
    ( ~ v1_funct_1(sK0)
    | sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,sK5(sK0,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1)))))
    | ~ v1_relat_1(sK0)
    | ~ spl7_13
    | ~ spl7_48 ),
    inference(resolution,[],[f445,f106])).

fof(f106,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK5(X0,X2)) = X2
        | ~ v1_relat_1(X0) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_13
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK5(X0,X2)) = X2
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f568,plain,
    ( sK5(sK0,sK2(sK0,sK1)) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK2(sK0,sK1))))
    | ~ spl7_14
    | ~ spl7_51 ),
    inference(resolution,[],[f473,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0 )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f473,plain,
    ( r2_hidden(sK5(sK0,sK2(sK0,sK1)),k2_relat_1(sK1))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl7_51
  <=> r2_hidden(sK5(sK0,sK2(sK0,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f660,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_55 ),
    inference(trivial_inequality_removal,[],[f656])).

fof(f656,plain,
    ( sK3(sK0,sK1) != sK3(sK0,sK1)
    | ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_34
    | ~ spl7_37
    | ~ spl7_55 ),
    inference(backward_demodulation,[],[f533,f587])).

fof(f652,plain,
    ( spl7_58
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_38
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f601,f373,f318,f139,f105,f61,f57,f650])).

fof(f373,plain,
    ( spl7_43
  <=> r2_hidden(sK5(sK1,sK3(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f601,plain,
    ( r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k2_relat_1(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_38
    | ~ spl7_43 ),
    inference(backward_demodulation,[],[f374,f599])).

fof(f599,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1)) = sK5(sK1,sK3(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_38
    | ~ spl7_43 ),
    inference(backward_demodulation,[],[f490,f596])).

fof(f596,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_13
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f595,f58])).

fof(f595,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_13
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f593,f62])).

fof(f593,plain,
    ( ~ v1_funct_1(sK1)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl7_13
    | ~ spl7_38 ),
    inference(resolution,[],[f319,f106])).

fof(f490,plain,
    ( sK5(sK1,sK3(sK0,sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1))))
    | ~ spl7_17
    | ~ spl7_43 ),
    inference(resolution,[],[f374,f140])).

fof(f374,plain,
    ( r2_hidden(sK5(sK1,sK3(sK0,sK1)),k2_relat_1(sK0))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f373])).

fof(f588,plain,
    ( spl7_55
    | spl7_38
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f381,f342,f85,f77,f61,f57,f318,f586])).

fof(f342,plain,
    ( spl7_40
  <=> ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k2_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f381,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f380,f78])).

fof(f380,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f379,f86])).

fof(f379,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f349,f58])).

fof(f349,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_2
    | ~ spl7_40 ),
    inference(resolution,[],[f343,f62])).

fof(f343,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK0,X0),k2_relat_1(sK1))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f342])).

fof(f564,plain,
    ( spl7_54
    | spl7_37
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f338,f322,f85,f77,f61,f57,f315,f562])).

fof(f322,plain,
    ( spl7_39
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f338,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f337,f78])).

fof(f337,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f336,f86])).

fof(f336,plain,
    ( k1_relat_1(sK1) != k2_relat_1(sK0)
    | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f334,f58])).

fof(f334,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_2
    | ~ spl7_39 ),
    inference(resolution,[],[f323,f62])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f322])).

fof(f474,plain,
    ( spl7_51
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f403,f315,f101,f81,f73,f69,f472])).

fof(f101,plain,
    ( spl7_12
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f403,plain,
    ( r2_hidden(sK5(sK0,sK2(sK0,sK1)),k2_relat_1(sK1))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f402,f82])).

fof(f402,plain,
    ( r2_hidden(sK5(sK0,sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f401,f70])).

fof(f401,plain,
    ( r2_hidden(sK5(sK0,sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f390,f74])).

fof(f390,plain,
    ( ~ v1_funct_1(sK0)
    | r2_hidden(sK5(sK0,sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(resolution,[],[f316,f102])).

fof(f102,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f470,plain,
    ( spl7_50
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f423,f413,f85,f61,f57,f468])).

fof(f413,plain,
    ( spl7_45
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1)))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

% (22842)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f423,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f422,f86])).

fof(f422,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0)))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f420,f58])).

fof(f420,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0)))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_45 ),
    inference(resolution,[],[f414,f62])).

fof(f414,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1)))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0)) )
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f413])).

fof(f446,plain,
    ( spl7_48
    | ~ spl7_37
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f438,f434,f315,f444])).

fof(f434,plain,
    ( spl7_47
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f438,plain,
    ( r2_hidden(sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))),k2_relat_1(sK0))
    | ~ spl7_37
    | ~ spl7_47 ),
    inference(resolution,[],[f435,f316])).

fof(f435,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0)) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f434])).

fof(f436,plain,
    ( spl7_47
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f408,f383,f85,f61,f57,f434])).

fof(f383,plain,
    ( spl7_44
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_44 ),
    inference(forward_demodulation,[],[f407,f86])).

fof(f407,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_44 ),
    inference(forward_demodulation,[],[f406,f86])).

fof(f406,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f404,f58])).

fof(f404,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_44 ),
    inference(resolution,[],[f384,f62])).

fof(f384,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0)) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f383])).

fof(f419,plain,
    ( spl7_46
    | ~ spl7_17
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f388,f315,f139,f417])).

fof(f388,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1)))
    | ~ spl7_17
    | ~ spl7_37 ),
    inference(resolution,[],[f316,f140])).

fof(f415,plain,
    ( spl7_45
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f121,f105,f97,f413])).

fof(f97,plain,
    ( spl7_11
  <=> ! [X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k1_relat_1(X0))
        | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1)))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0)) )
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1)))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(resolution,[],[f106,f98])).

fof(f98,plain,
    ( ! [X0,X3] :
        ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f385,plain,
    ( spl7_44
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f119,f101,f97,f383])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0)) )
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f102,f98])).

fof(f375,plain,
    ( spl7_43
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f333,f318,f101,f85,f61,f57,f373])).

fof(f333,plain,
    ( r2_hidden(sK5(sK1,sK3(sK0,sK1)),k2_relat_1(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f332,f86])).

fof(f332,plain,
    ( r2_hidden(sK5(sK1,sK3(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f331,f58])).

fof(f331,plain,
    ( r2_hidden(sK5(sK1,sK3(sK0,sK1)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f328,f62])).

fof(f328,plain,
    ( ~ v1_funct_1(sK1)
    | r2_hidden(sK5(sK1,sK3(sK0,sK1)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_12
    | ~ spl7_38 ),
    inference(resolution,[],[f319,f102])).

fof(f364,plain,
    ( spl7_42
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f283,f266,f73,f69,f65,f362])).

fof(f266,plain,
    ( spl7_33
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
        | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        | k2_funct_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f282,f70])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f281,f74])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_33 ),
    inference(resolution,[],[f267,f66])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
        | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        | k2_funct_1(X0) = X1 )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f266])).

fof(f348,plain,
    ( spl7_41
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f326,f318,f123,f346])).

fof(f326,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1)))
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(resolution,[],[f319,f124])).

fof(f344,plain,
    ( spl7_40
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f257,f231,f81,f73,f69,f65,f342])).

fof(f231,plain,
    ( spl7_29
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
        | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | k2_funct_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f257,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k2_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_29 ),
    inference(forward_demodulation,[],[f256,f82])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f255,f70])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f254,f74])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_29 ),
    inference(resolution,[],[f232,f66])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
        | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | k2_funct_1(X0) = X1 )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f231])).

fof(f324,plain,
    ( spl7_39
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f260,f239,f73,f69,f65,f322])).

fof(f239,plain,
    ( spl7_31
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
        | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        | k2_funct_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f259,f70])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f258,f74])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_31 ),
    inference(resolution,[],[f240,f66])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
        | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        | k2_funct_1(X0) = X1 )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f239])).

fof(f320,plain,
    ( spl7_37
    | spl7_38
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f310,f303,f85,f77,f61,f57,f318,f315])).

fof(f303,plain,
    ( spl7_36
  <=> ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k2_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f310,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_6
    | ~ spl7_8
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f309,f78])).

fof(f309,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f308,f86])).

fof(f308,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f306,f58])).

fof(f306,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK1 = k2_funct_1(sK0)
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(resolution,[],[f304,f62])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK0,X0),k2_relat_1(sK1))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( spl7_36
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f229,f218,f81,f73,f69,f65,f303])).

fof(f218,plain,
    ( spl7_28
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
        | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | k2_funct_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f229,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k2_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f228,f82])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f227,f70])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f226,f74])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k2_funct_1(sK0) = X0 )
    | ~ spl7_3
    | ~ spl7_28 ),
    inference(resolution,[],[f219,f66])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X0) != k1_relat_1(X1)
        | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
        | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
        | k2_funct_1(X0) = X1 )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f218])).

fof(f287,plain,(
    spl7_34 ),
    inference(avatar_split_clause,[],[f23,f285])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
      | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f268,plain,(
    spl7_33 ),
    inference(avatar_split_clause,[],[f27,f266])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f241,plain,(
    spl7_31 ),
    inference(avatar_split_clause,[],[f29,f239])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f233,plain,(
    spl7_29 ),
    inference(avatar_split_clause,[],[f26,f231])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f220,plain,(
    spl7_28 ),
    inference(avatar_split_clause,[],[f28,f218])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f141,plain,
    ( spl7_17
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f117,f97,f93,f85,f61,f57,f139])).

fof(f93,plain,
    ( spl7_10
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK0))
        | ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f117,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1 )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1 )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f115,f86])).

fof(f115,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1 )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f114,f58])).

fof(f114,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1 )
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f109,f62])).

fof(f109,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1 )
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(resolution,[],[f98,f94])).

fof(f94,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
        | ~ r2_hidden(X3,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f125,plain,
    ( spl7_14
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f113,f97,f89,f81,f73,f69,f123])).

fof(f89,plain,
    ( spl7_9
  <=> ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK0,X2),k2_relat_1(sK0))
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0 )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0 )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f111,f82])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0 )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f110,f70])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0 )
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f108,f74])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0 )
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(resolution,[],[f98,f90])).

fof(f90,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK0,X2),k2_relat_1(sK0))
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f107,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f50,f105])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f103,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f51,f101])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f99,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f49,f97])).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f55,f93])).

fof(f55,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK0))
      | ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(forward_demodulation,[],[f54,f17])).

fof(f17,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k2_relat_1(X0) = k1_relat_1(X1)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(f54,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(forward_demodulation,[],[f38,f16])).

fof(f16,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) != X2
      | k1_funct_1(sK0,X2) = X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f91,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f53,f89])).

fof(f53,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_funct_1(sK0,X2),k2_relat_1(sK0))
      | ~ r2_hidden(X2,k2_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 ) ),
    inference(forward_demodulation,[],[f52,f17])).

fof(f52,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK1))
      | ~ r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 ) ),
    inference(forward_demodulation,[],[f37,f16])).

fof(f37,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) = X2
      | k1_funct_1(sK0,X2) != X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f17,f85])).

fof(f83,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f16,f81])).

fof(f79,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f18,f77])).

fof(f18,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f20,f73])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f19,f69])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f15,f65])).

fof(f15,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f14,f61])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f13,f57])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:41:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (22840)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (22832)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (22835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (22843)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (22833)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (22834)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (22829)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (22825)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (22843)Refutation not found, incomplete strategy% (22843)------------------------------
% 0.22/0.50  % (22843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22843)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22843)Memory used [KB]: 10618
% 0.22/0.50  % (22843)Time elapsed: 0.072 s
% 0.22/0.50  % (22843)------------------------------
% 0.22/0.50  % (22843)------------------------------
% 0.22/0.50  % (22839)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (22826)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (22824)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (22823)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (22841)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (22827)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (22828)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (22838)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (22836)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (22831)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (22837)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (22832)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (22830)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f876,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f125,f141,f220,f233,f241,f268,f287,f305,f320,f324,f344,f348,f364,f375,f385,f415,f419,f436,f446,f470,f474,f564,f588,f652,f702,f823,f836,f875])).
% 0.22/0.52  fof(f875,plain,(
% 0.22/0.52    spl7_37 | ~spl7_54 | ~spl7_58),
% 0.22/0.52    inference(avatar_split_clause,[],[f826,f650,f562,f315])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    spl7_37 <=> r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.52  fof(f562,plain,(
% 0.22/0.52    spl7_54 <=> sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 0.22/0.52  fof(f650,plain,(
% 0.22/0.52    spl7_58 <=> r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 0.22/0.52  fof(f826,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | (~spl7_54 | ~spl7_58)),
% 0.22/0.52    inference(backward_demodulation,[],[f651,f563])).
% 0.22/0.52  fof(f563,plain,(
% 0.22/0.52    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | ~spl7_54),
% 0.22/0.52    inference(avatar_component_clause,[],[f562])).
% 0.22/0.52  fof(f651,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k2_relat_1(sK0)) | ~spl7_58),
% 0.22/0.52    inference(avatar_component_clause,[],[f650])).
% 0.22/0.52  fof(f836,plain,(
% 0.22/0.52    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37 | ~spl7_38 | ~spl7_41 | ~spl7_54),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f835])).
% 0.22/0.52  fof(f835,plain,(
% 0.22/0.52    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37 | ~spl7_38 | ~spl7_41 | ~spl7_54)),
% 0.22/0.52    inference(subsumption_resolution,[],[f834,f824])).
% 0.22/0.52  fof(f824,plain,(
% 0.22/0.52    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl7_41 | ~spl7_54)),
% 0.22/0.52    inference(backward_demodulation,[],[f347,f563])).
% 0.22/0.52  fof(f347,plain,(
% 0.22/0.52    sK3(sK0,sK1) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1))) | ~spl7_41),
% 0.22/0.52    inference(avatar_component_clause,[],[f346])).
% 0.22/0.52  fof(f346,plain,(
% 0.22/0.52    spl7_41 <=> sK3(sK0,sK1) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.22/0.52  fof(f834,plain,(
% 0.22/0.52    sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37 | ~spl7_38 | ~spl7_54)),
% 0.22/0.52    inference(subsumption_resolution,[],[f829,f319])).
% 0.22/0.52  fof(f319,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | ~spl7_38),
% 0.22/0.52    inference(avatar_component_clause,[],[f318])).
% 0.22/0.52  fof(f318,plain,(
% 0.22/0.52    spl7_38 <=> r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.52  fof(f829,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37 | ~spl7_54)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f825])).
% 0.22/0.52  fof(f825,plain,(
% 0.22/0.52    sK2(sK0,sK1) != sK2(sK0,sK1) | ~r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37 | ~spl7_54)),
% 0.22/0.52    inference(backward_demodulation,[],[f533,f563])).
% 0.22/0.52  fof(f533,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(forward_demodulation,[],[f532,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(sK1) | ~spl7_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl7_7 <=> k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.52  fof(f532,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_8 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f531,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    sK1 != k2_funct_1(sK0) | spl7_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl7_6 <=> sK1 = k2_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.52  fof(f531,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_8 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f530,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl7_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl7_4 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.52  fof(f530,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_relat_1(sK0) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_8 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f529,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    k1_relat_1(sK1) = k2_relat_1(sK0) | ~spl7_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl7_8 <=> k1_relat_1(sK1) = k2_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.52  fof(f529,plain,(
% 0.22/0.52    k1_relat_1(sK1) != k2_relat_1(sK0) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_relat_1(sK0) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f528,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    v1_funct_1(sK1) | ~spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl7_2 <=> v1_funct_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f528,plain,(
% 0.22/0.52    ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_relat_1(sK0) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f527,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    v1_relat_1(sK1) | ~spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl7_1 <=> v1_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f527,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_relat_1(sK0) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_3 | ~spl7_5 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f526,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    v2_funct_1(sK0) | ~spl7_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl7_3 <=> v2_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.52  fof(f526,plain,(
% 0.22/0.52    ~v2_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_relat_1(sK0) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_5 | ~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f519,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    v1_funct_1(sK0) | ~spl7_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl7_5 <=> v1_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.52  fof(f519,plain,(
% 0.22/0.52    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_relat_1(sK0) | sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_34 | ~spl7_37)),
% 0.22/0.52    inference(resolution,[],[f316,f286])).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~v1_relat_1(X0) | sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k2_funct_1(X0) = X1) ) | ~spl7_34),
% 0.22/0.52    inference(avatar_component_clause,[],[f285])).
% 0.22/0.52  fof(f285,plain,(
% 0.22/0.52    spl7_34 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k2_funct_1(X0) = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.52  fof(f316,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~spl7_37),
% 0.22/0.52    inference(avatar_component_clause,[],[f315])).
% 0.22/0.52  fof(f823,plain,(
% 0.22/0.52    spl7_54 | spl7_55 | ~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_42),
% 0.22/0.52    inference(avatar_split_clause,[],[f369,f362,f85,f77,f61,f57,f586,f562])).
% 0.22/0.52  fof(f586,plain,(
% 0.22/0.52    spl7_55 <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 0.22/0.52  fof(f362,plain,(
% 0.22/0.52    spl7_42 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.22/0.52  fof(f369,plain,(
% 0.22/0.52    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | (~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_42)),
% 0.22/0.52    inference(subsumption_resolution,[],[f368,f78])).
% 0.22/0.52  fof(f368,plain,(
% 0.22/0.52    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_42)),
% 0.22/0.52    inference(subsumption_resolution,[],[f367,f86])).
% 0.22/0.52  fof(f367,plain,(
% 0.22/0.52    k1_relat_1(sK1) != k2_relat_1(sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_42)),
% 0.22/0.52    inference(subsumption_resolution,[],[f365,f58])).
% 0.22/0.52  fof(f365,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_2 | ~spl7_42)),
% 0.22/0.52    inference(resolution,[],[f363,f62])).
% 0.22/0.52  fof(f363,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | ~spl7_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f362])).
% 0.22/0.52  fof(f702,plain,(
% 0.22/0.52    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_13 | ~spl7_14 | ~spl7_17 | ~spl7_34 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50 | ~spl7_51 | ~spl7_55),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f701])).
% 0.22/0.52  fof(f701,plain,(
% 0.22/0.52    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_13 | ~spl7_14 | ~spl7_17 | ~spl7_34 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50 | ~spl7_51 | ~spl7_55)),
% 0.22/0.52    inference(subsumption_resolution,[],[f700,f653])).
% 0.22/0.52  fof(f653,plain,(
% 0.22/0.52    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | (~spl7_46 | ~spl7_55)),
% 0.22/0.52    inference(backward_demodulation,[],[f418,f587])).
% 0.22/0.52  fof(f587,plain,(
% 0.22/0.52    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~spl7_55),
% 0.22/0.52    inference(avatar_component_clause,[],[f586])).
% 0.22/0.52  fof(f418,plain,(
% 0.22/0.52    sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) | ~spl7_46),
% 0.22/0.52    inference(avatar_component_clause,[],[f417])).
% 0.22/0.52  fof(f417,plain,(
% 0.22/0.52    spl7_46 <=> sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.22/0.52  fof(f700,plain,(
% 0.22/0.52    sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_13 | ~spl7_14 | ~spl7_17 | ~spl7_34 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50 | ~spl7_51 | ~spl7_55)),
% 0.22/0.52    inference(subsumption_resolution,[],[f660,f659])).
% 0.22/0.52  fof(f659,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | (~spl7_4 | ~spl7_5 | ~spl7_13 | ~spl7_14 | ~spl7_17 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50 | ~spl7_51 | ~spl7_55)),
% 0.22/0.52    inference(backward_demodulation,[],[f576,f587])).
% 0.22/0.52  fof(f576,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k2_relat_1(sK1)) | (~spl7_4 | ~spl7_5 | ~spl7_13 | ~spl7_14 | ~spl7_17 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50 | ~spl7_51)),
% 0.22/0.52    inference(backward_demodulation,[],[f473,f574])).
% 0.22/0.52  fof(f574,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK0,sK2(sK0,sK1)) | (~spl7_4 | ~spl7_5 | ~spl7_13 | ~spl7_14 | ~spl7_17 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50 | ~spl7_51)),
% 0.22/0.52    inference(forward_demodulation,[],[f568,f539])).
% 0.22/0.52  fof(f539,plain,(
% 0.22/0.52    sK2(sK0,sK1) = k1_funct_1(sK0,sK5(sK0,sK2(sK0,sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_13 | ~spl7_17 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50)),
% 0.22/0.52    inference(backward_demodulation,[],[f457,f537])).
% 0.22/0.52  fof(f537,plain,(
% 0.22/0.52    sK2(sK0,sK1) = sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) | (~spl7_17 | ~spl7_37 | ~spl7_46 | ~spl7_48 | ~spl7_50)),
% 0.22/0.52    inference(forward_demodulation,[],[f535,f418])).
% 0.22/0.52  fof(f535,plain,(
% 0.22/0.52    k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) = sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) | (~spl7_17 | ~spl7_37 | ~spl7_48 | ~spl7_50)),
% 0.22/0.52    inference(backward_demodulation,[],[f453,f520])).
% 0.22/0.52  fof(f520,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1)))) | (~spl7_37 | ~spl7_50)),
% 0.22/0.52    inference(resolution,[],[f316,f469])).
% 0.22/0.52  fof(f469,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0)))) ) | ~spl7_50),
% 0.22/0.52    inference(avatar_component_clause,[],[f468])).
% 0.22/0.52  fof(f468,plain,(
% 0.22/0.52    spl7_50 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 0.22/0.52  fof(f453,plain,(
% 0.22/0.52    sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))))) | (~spl7_17 | ~spl7_48)),
% 0.22/0.52    inference(resolution,[],[f445,f140])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1) ) | ~spl7_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    spl7_17 <=> ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.52  fof(f445,plain,(
% 0.22/0.52    r2_hidden(sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))),k2_relat_1(sK0)) | ~spl7_48),
% 0.22/0.52    inference(avatar_component_clause,[],[f444])).
% 0.22/0.52  fof(f444,plain,(
% 0.22/0.52    spl7_48 <=> r2_hidden(sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.22/0.52  fof(f457,plain,(
% 0.22/0.52    sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,sK5(sK0,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))))) | (~spl7_4 | ~spl7_5 | ~spl7_13 | ~spl7_48)),
% 0.22/0.52    inference(subsumption_resolution,[],[f456,f70])).
% 0.22/0.52  fof(f456,plain,(
% 0.22/0.52    sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,sK5(sK0,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))))) | ~v1_relat_1(sK0) | (~spl7_5 | ~spl7_13 | ~spl7_48)),
% 0.22/0.52    inference(subsumption_resolution,[],[f454,f74])).
% 0.22/0.52  fof(f454,plain,(
% 0.22/0.52    ~v1_funct_1(sK0) | sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))) = k1_funct_1(sK0,sK5(sK0,sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))))) | ~v1_relat_1(sK0) | (~spl7_13 | ~spl7_48)),
% 0.22/0.52    inference(resolution,[],[f445,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X2)) = X2 | ~v1_relat_1(X0)) ) | ~spl7_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f105])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    spl7_13 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.52  fof(f568,plain,(
% 0.22/0.52    sK5(sK0,sK2(sK0,sK1)) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK2(sK0,sK1)))) | (~spl7_14 | ~spl7_51)),
% 0.22/0.52    inference(resolution,[],[f473,f124])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0) ) | ~spl7_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f123])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl7_14 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.52  fof(f473,plain,(
% 0.22/0.52    r2_hidden(sK5(sK0,sK2(sK0,sK1)),k2_relat_1(sK1)) | ~spl7_51),
% 0.22/0.52    inference(avatar_component_clause,[],[f472])).
% 0.22/0.52  fof(f472,plain,(
% 0.22/0.52    spl7_51 <=> r2_hidden(sK5(sK0,sK2(sK0,sK1)),k2_relat_1(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 0.22/0.52  fof(f660,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37 | ~spl7_55)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f656])).
% 0.22/0.52  fof(f656,plain,(
% 0.22/0.52    sK3(sK0,sK1) != sK3(sK0,sK1) | ~r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_34 | ~spl7_37 | ~spl7_55)),
% 0.22/0.52    inference(backward_demodulation,[],[f533,f587])).
% 0.22/0.52  fof(f652,plain,(
% 0.22/0.52    spl7_58 | ~spl7_1 | ~spl7_2 | ~spl7_13 | ~spl7_17 | ~spl7_38 | ~spl7_43),
% 0.22/0.52    inference(avatar_split_clause,[],[f601,f373,f318,f139,f105,f61,f57,f650])).
% 0.22/0.52  fof(f373,plain,(
% 0.22/0.52    spl7_43 <=> r2_hidden(sK5(sK1,sK3(sK0,sK1)),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.22/0.52  fof(f601,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k2_relat_1(sK0)) | (~spl7_1 | ~spl7_2 | ~spl7_13 | ~spl7_17 | ~spl7_38 | ~spl7_43)),
% 0.22/0.52    inference(backward_demodulation,[],[f374,f599])).
% 0.22/0.52  fof(f599,plain,(
% 0.22/0.52    k1_funct_1(sK0,sK3(sK0,sK1)) = sK5(sK1,sK3(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_13 | ~spl7_17 | ~spl7_38 | ~spl7_43)),
% 0.22/0.52    inference(backward_demodulation,[],[f490,f596])).
% 0.22/0.52  fof(f596,plain,(
% 0.22/0.52    sK3(sK0,sK1) = k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1))) | (~spl7_1 | ~spl7_2 | ~spl7_13 | ~spl7_38)),
% 0.22/0.52    inference(subsumption_resolution,[],[f595,f58])).
% 0.22/0.52  fof(f595,plain,(
% 0.22/0.52    sK3(sK0,sK1) = k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1))) | ~v1_relat_1(sK1) | (~spl7_2 | ~spl7_13 | ~spl7_38)),
% 0.22/0.52    inference(subsumption_resolution,[],[f593,f62])).
% 0.22/0.52  fof(f593,plain,(
% 0.22/0.52    ~v1_funct_1(sK1) | sK3(sK0,sK1) = k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1))) | ~v1_relat_1(sK1) | (~spl7_13 | ~spl7_38)),
% 0.22/0.52    inference(resolution,[],[f319,f106])).
% 0.22/0.52  fof(f490,plain,(
% 0.22/0.52    sK5(sK1,sK3(sK0,sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,sK3(sK0,sK1)))) | (~spl7_17 | ~spl7_43)),
% 0.22/0.52    inference(resolution,[],[f374,f140])).
% 0.22/0.52  fof(f374,plain,(
% 0.22/0.52    r2_hidden(sK5(sK1,sK3(sK0,sK1)),k2_relat_1(sK0)) | ~spl7_43),
% 0.22/0.52    inference(avatar_component_clause,[],[f373])).
% 0.22/0.52  fof(f588,plain,(
% 0.22/0.52    spl7_55 | spl7_38 | ~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_40),
% 0.22/0.52    inference(avatar_split_clause,[],[f381,f342,f85,f77,f61,f57,f318,f586])).
% 0.22/0.52  fof(f342,plain,(
% 0.22/0.52    spl7_40 <=> ! [X0] : (r2_hidden(sK3(sK0,X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k2_funct_1(sK0) = X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.22/0.52  fof(f381,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_40)),
% 0.22/0.52    inference(subsumption_resolution,[],[f380,f78])).
% 0.22/0.52  fof(f380,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_40)),
% 0.22/0.52    inference(subsumption_resolution,[],[f379,f86])).
% 0.22/0.52  fof(f379,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_40)),
% 0.22/0.52    inference(subsumption_resolution,[],[f349,f58])).
% 0.22/0.52  fof(f349,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_2 | ~spl7_40)),
% 0.22/0.52    inference(resolution,[],[f343,f62])).
% 0.22/0.52  fof(f343,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(sK0,X0),k2_relat_1(sK1)) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k2_funct_1(sK0) = X0) ) | ~spl7_40),
% 0.22/0.52    inference(avatar_component_clause,[],[f342])).
% 0.22/0.52  fof(f564,plain,(
% 0.22/0.52    spl7_54 | spl7_37 | ~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_39),
% 0.22/0.52    inference(avatar_split_clause,[],[f338,f322,f85,f77,f61,f57,f315,f562])).
% 0.22/0.52  fof(f322,plain,(
% 0.22/0.52    spl7_39 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.52  fof(f338,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | (~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_39)),
% 0.22/0.52    inference(subsumption_resolution,[],[f337,f78])).
% 0.22/0.52  fof(f337,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_39)),
% 0.22/0.52    inference(subsumption_resolution,[],[f336,f86])).
% 0.22/0.52  fof(f336,plain,(
% 0.22/0.52    k1_relat_1(sK1) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_39)),
% 0.22/0.52    inference(subsumption_resolution,[],[f334,f58])).
% 0.22/0.52  fof(f334,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK1 = k2_funct_1(sK0) | (~spl7_2 | ~spl7_39)),
% 0.22/0.52    inference(resolution,[],[f323,f62])).
% 0.22/0.52  fof(f323,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | ~spl7_39),
% 0.22/0.52    inference(avatar_component_clause,[],[f322])).
% 0.22/0.52  fof(f474,plain,(
% 0.22/0.52    spl7_51 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_12 | ~spl7_37),
% 0.22/0.52    inference(avatar_split_clause,[],[f403,f315,f101,f81,f73,f69,f472])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl7_12 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    r2_hidden(sK5(sK0,sK2(sK0,sK1)),k2_relat_1(sK1)) | (~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_12 | ~spl7_37)),
% 0.22/0.52    inference(forward_demodulation,[],[f402,f82])).
% 0.22/0.52  fof(f402,plain,(
% 0.22/0.52    r2_hidden(sK5(sK0,sK2(sK0,sK1)),k1_relat_1(sK0)) | (~spl7_4 | ~spl7_5 | ~spl7_12 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f401,f70])).
% 0.22/0.52  fof(f401,plain,(
% 0.22/0.52    r2_hidden(sK5(sK0,sK2(sK0,sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl7_5 | ~spl7_12 | ~spl7_37)),
% 0.22/0.52    inference(subsumption_resolution,[],[f390,f74])).
% 0.22/0.52  fof(f390,plain,(
% 0.22/0.52    ~v1_funct_1(sK0) | r2_hidden(sK5(sK0,sK2(sK0,sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl7_12 | ~spl7_37)),
% 0.22/0.52    inference(resolution,[],[f316,f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl7_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f101])).
% 0.22/0.52  fof(f470,plain,(
% 0.22/0.52    spl7_50 | ~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_45),
% 0.22/0.52    inference(avatar_split_clause,[],[f423,f413,f85,f61,f57,f468])).
% 0.22/0.52  fof(f413,plain,(
% 0.22/0.52    spl7_45 <=> ! [X1,X0] : (~v1_funct_1(X0) | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1))) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.22/0.53  % (22842)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  fof(f423,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0)))) ) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_45)),
% 0.22/0.53    inference(forward_demodulation,[],[f422,f86])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0))) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl7_1 | ~spl7_2 | ~spl7_45)),
% 0.22/0.53    inference(subsumption_resolution,[],[f420,f58])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(sK1,sK5(sK1,k1_funct_1(sK1,X0))) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl7_2 | ~spl7_45)),
% 0.22/0.53    inference(resolution,[],[f414,f62])).
% 0.22/0.53  fof(f414,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1))) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0))) ) | ~spl7_45),
% 0.22/0.53    inference(avatar_component_clause,[],[f413])).
% 0.22/0.53  fof(f446,plain,(
% 0.22/0.53    spl7_48 | ~spl7_37 | ~spl7_47),
% 0.22/0.53    inference(avatar_split_clause,[],[f438,f434,f315,f444])).
% 0.22/0.53  fof(f434,plain,(
% 0.22/0.53    spl7_47 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.22/0.53  fof(f438,plain,(
% 0.22/0.53    r2_hidden(sK5(sK1,k1_funct_1(sK1,sK2(sK0,sK1))),k2_relat_1(sK0)) | (~spl7_37 | ~spl7_47)),
% 0.22/0.53    inference(resolution,[],[f435,f316])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0))) ) | ~spl7_47),
% 0.22/0.53    inference(avatar_component_clause,[],[f434])).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    spl7_47 | ~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_44),
% 0.22/0.53    inference(avatar_split_clause,[],[f408,f383,f85,f61,f57,f434])).
% 0.22/0.53  fof(f383,plain,(
% 0.22/0.53    spl7_44 <=> ! [X1,X0] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.22/0.53  fof(f408,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0))) ) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_44)),
% 0.22/0.53    inference(forward_demodulation,[],[f407,f86])).
% 0.22/0.53  fof(f407,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k2_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_44)),
% 0.22/0.53    inference(forward_demodulation,[],[f406,f86])).
% 0.22/0.53  fof(f406,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl7_1 | ~spl7_2 | ~spl7_44)),
% 0.22/0.53    inference(subsumption_resolution,[],[f404,f58])).
% 0.22/0.53  fof(f404,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK5(sK1,k1_funct_1(sK1,X0)),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl7_2 | ~spl7_44)),
% 0.22/0.53    inference(resolution,[],[f384,f62])).
% 0.22/0.53  fof(f384,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0))) ) | ~spl7_44),
% 0.22/0.53    inference(avatar_component_clause,[],[f383])).
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    spl7_46 | ~spl7_17 | ~spl7_37),
% 0.22/0.53    inference(avatar_split_clause,[],[f388,f315,f139,f417])).
% 0.22/0.53  fof(f388,plain,(
% 0.22/0.53    sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) | (~spl7_17 | ~spl7_37)),
% 0.22/0.53    inference(resolution,[],[f316,f140])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    spl7_45 | ~spl7_11 | ~spl7_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f121,f105,f97,f413])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl7_11 <=> ! [X3,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1))) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0))) ) | (~spl7_11 | ~spl7_13)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,X1) = k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1))) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl7_11 | ~spl7_13)),
% 0.22/0.53    inference(resolution,[],[f106,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl7_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f97])).
% 0.22/0.53  fof(f385,plain,(
% 0.22/0.53    spl7_44 | ~spl7_11 | ~spl7_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f119,f101,f97,f383])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0))) ) | (~spl7_11 | ~spl7_12)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,k1_funct_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl7_11 | ~spl7_12)),
% 0.22/0.53    inference(resolution,[],[f102,f98])).
% 0.22/0.53  fof(f375,plain,(
% 0.22/0.53    spl7_43 | ~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_12 | ~spl7_38),
% 0.22/0.53    inference(avatar_split_clause,[],[f333,f318,f101,f85,f61,f57,f373])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    r2_hidden(sK5(sK1,sK3(sK0,sK1)),k2_relat_1(sK0)) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_12 | ~spl7_38)),
% 0.22/0.53    inference(forward_demodulation,[],[f332,f86])).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    r2_hidden(sK5(sK1,sK3(sK0,sK1)),k1_relat_1(sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_12 | ~spl7_38)),
% 0.22/0.53    inference(subsumption_resolution,[],[f331,f58])).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    r2_hidden(sK5(sK1,sK3(sK0,sK1)),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl7_2 | ~spl7_12 | ~spl7_38)),
% 0.22/0.53    inference(subsumption_resolution,[],[f328,f62])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    ~v1_funct_1(sK1) | r2_hidden(sK5(sK1,sK3(sK0,sK1)),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl7_12 | ~spl7_38)),
% 0.22/0.53    inference(resolution,[],[f319,f102])).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    spl7_42 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_33),
% 0.22/0.53    inference(avatar_split_clause,[],[f283,f266,f73,f69,f65,f362])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    spl7_33 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_funct_1(X0) = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_33)),
% 0.22/0.53    inference(subsumption_resolution,[],[f282,f70])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_5 | ~spl7_33)),
% 0.22/0.53    inference(subsumption_resolution,[],[f281,f74])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_33)),
% 0.22/0.53    inference(resolution,[],[f267,f66])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_funct_1(X0) = X1) ) | ~spl7_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f266])).
% 0.22/0.53  fof(f348,plain,(
% 0.22/0.53    spl7_41 | ~spl7_14 | ~spl7_38),
% 0.22/0.53    inference(avatar_split_clause,[],[f326,f318,f123,f346])).
% 0.22/0.53  fof(f326,plain,(
% 0.22/0.53    sK3(sK0,sK1) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1))) | (~spl7_14 | ~spl7_38)),
% 0.22/0.53    inference(resolution,[],[f319,f124])).
% 0.22/0.53  fof(f344,plain,(
% 0.22/0.53    spl7_40 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f257,f231,f81,f73,f69,f65,f342])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    spl7_29 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_funct_1(X0) = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_29)),
% 0.22/0.53    inference(forward_demodulation,[],[f256,f82])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_29)),
% 0.22/0.53    inference(subsumption_resolution,[],[f255,f70])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_5 | ~spl7_29)),
% 0.22/0.53    inference(subsumption_resolution,[],[f254,f74])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_29)),
% 0.22/0.53    inference(resolution,[],[f232,f66])).
% 0.22/0.53  fof(f232,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_funct_1(X0) = X1) ) | ~spl7_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f231])).
% 0.22/0.53  fof(f324,plain,(
% 0.22/0.53    spl7_39 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f260,f239,f73,f69,f65,f322])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    spl7_31 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_funct_1(X0) = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_31)),
% 0.22/0.53    inference(subsumption_resolution,[],[f259,f70])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_5 | ~spl7_31)),
% 0.22/0.53    inference(subsumption_resolution,[],[f258,f74])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_31)),
% 0.22/0.53    inference(resolution,[],[f240,f66])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_funct_1(X0) = X1) ) | ~spl7_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f239])).
% 0.22/0.53  fof(f320,plain,(
% 0.22/0.53    spl7_37 | spl7_38 | ~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_36),
% 0.22/0.53    inference(avatar_split_clause,[],[f310,f303,f85,f77,f61,f57,f318,f315])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    spl7_36 <=> ! [X0] : (r2_hidden(sK3(sK0,X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k2_funct_1(sK0) = X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | (~spl7_1 | ~spl7_2 | spl7_6 | ~spl7_8 | ~spl7_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f309,f78])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f308,f86])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK1 = k2_funct_1(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f306,f58])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    ~v1_relat_1(sK1) | r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK1 = k2_funct_1(sK0) | (~spl7_2 | ~spl7_36)),
% 0.22/0.53    inference(resolution,[],[f304,f62])).
% 0.22/0.53  fof(f304,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(sK0,X0),k2_relat_1(sK1)) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | ~spl7_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f303])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    spl7_36 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f229,f218,f81,f73,f69,f65,f303])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl7_28 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_funct_1(X0) = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_28)),
% 0.22/0.53    inference(forward_demodulation,[],[f228,f82])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_28)),
% 0.22/0.53    inference(subsumption_resolution,[],[f227,f70])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_5 | ~spl7_28)),
% 0.22/0.53    inference(subsumption_resolution,[],[f226,f74])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k2_funct_1(sK0) = X0) ) | (~spl7_3 | ~spl7_28)),
% 0.22/0.53    inference(resolution,[],[f219,f66])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_funct_1(X0) = X1) ) | ~spl7_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f218])).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    spl7_34),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f285])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k2_funct_1(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    spl7_33),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f266])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_funct_1(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    spl7_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f239])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_funct_1(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    spl7_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f231])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    spl7_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f218])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    spl7_17 | ~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_10 | ~spl7_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f117,f97,f93,f85,f61,f57,f139])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl7_10 <=> ! [X3] : (~r2_hidden(X3,k2_relat_1(sK0)) | ~r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1) ) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_10 | ~spl7_11)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | ~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1) ) | (~spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_10 | ~spl7_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f115,f86])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1) ) | (~spl7_1 | ~spl7_2 | ~spl7_10 | ~spl7_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f114,f58])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1) ) | (~spl7_2 | ~spl7_10 | ~spl7_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f62])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X1] : (~v1_funct_1(sK1) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X1)) = X1) ) | (~spl7_10 | ~spl7_11)),
% 0.22/0.53    inference(resolution,[],[f98,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1)) | ~r2_hidden(X3,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) ) | ~spl7_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f93])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl7_14 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_9 | ~spl7_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f113,f97,f89,f81,f73,f69,f123])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl7_9 <=> ! [X2] : (~r2_hidden(k1_funct_1(sK0,X2),k2_relat_1(sK0)) | ~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0) ) | (~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0) ) | (~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_9 | ~spl7_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f111,f82])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0) ) | (~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f110,f70])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0) ) | (~spl7_5 | ~spl7_9 | ~spl7_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f108,f74])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X0) ) | (~spl7_9 | ~spl7_11)),
% 0.22/0.53    inference(resolution,[],[f98,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(k1_funct_1(sK0,X2),k2_relat_1(sK0)) | ~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2) ) | ~spl7_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl7_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f105])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl7_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f51,f101])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl7_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f97])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(equality_resolution,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl7_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f93])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK0)) | ~r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.22/0.53    inference(forward_demodulation,[],[f54,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    k1_relat_1(sK1) = k2_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f5])).
% 0.22/0.53  fof(f5,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f3])).
% 0.22/0.53  fof(f3,conjecture,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.22/0.53    inference(forward_demodulation,[],[f38,f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.22/0.53    inference(equality_resolution,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) != X2 | k1_funct_1(sK0,X2) = X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl7_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f53,f89])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(k1_funct_1(sK0,X2),k2_relat_1(sK0)) | ~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2) )),
% 0.22/0.53    inference(forward_demodulation,[],[f52,f17])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2) )),
% 0.22/0.53    inference(forward_demodulation,[],[f37,f16])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl7_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f17,f85])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl7_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f16,f81])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ~spl7_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f18,f77])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    sK1 != k2_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl7_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f73])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    v1_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl7_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f19,f69])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl7_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f15,f65])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    v2_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl7_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f14,f61])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl7_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f13,f57])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (22832)------------------------------
% 0.22/0.53  % (22832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22832)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (22832)Memory used [KB]: 11129
% 0.22/0.53  % (22832)Time elapsed: 0.092 s
% 0.22/0.53  % (22832)------------------------------
% 0.22/0.53  % (22832)------------------------------
% 0.22/0.53  % (22822)Success in time 0.166 s
%------------------------------------------------------------------------------
