%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 365 expanded)
%              Number of leaves         :   60 ( 173 expanded)
%              Depth                    :    7
%              Number of atoms          :  633 ( 990 expanded)
%              Number of equality atoms :   97 ( 162 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f974,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f73,f78,f83,f87,f91,f95,f99,f104,f108,f112,f116,f135,f162,f168,f172,f183,f191,f203,f211,f247,f257,f267,f284,f327,f332,f336,f456,f490,f536,f689,f738,f782,f810,f828,f836,f846,f925,f949,f954,f964])).

fof(f964,plain,
    ( ~ spl1_7
    | spl1_23
    | ~ spl1_90 ),
    inference(avatar_contradiction_clause,[],[f963])).

fof(f963,plain,
    ( $false
    | ~ spl1_7
    | spl1_23
    | ~ spl1_90 ),
    inference(subsumption_resolution,[],[f956,f178])).

fof(f178,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_23 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl1_23
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f956,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_7
    | ~ spl1_90 ),
    inference(resolution,[],[f944,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f944,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_90 ),
    inference(avatar_component_clause,[],[f942])).

fof(f942,plain,
    ( spl1_90
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_90])])).

fof(f954,plain,
    ( ~ spl1_1
    | ~ spl1_20
    | ~ spl1_22
    | spl1_91 ),
    inference(avatar_contradiction_clause,[],[f953])).

fof(f953,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_20
    | ~ spl1_22
    | spl1_91 ),
    inference(subsumption_resolution,[],[f952,f155])).

fof(f155,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl1_20
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f952,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_22
    | spl1_91 ),
    inference(subsumption_resolution,[],[f950,f63])).

fof(f63,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f950,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_22
    | spl1_91 ),
    inference(resolution,[],[f948,f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl1_22
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f948,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_91 ),
    inference(avatar_component_clause,[],[f946])).

fof(f946,plain,
    ( spl1_91
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_91])])).

fof(f949,plain,
    ( spl1_90
    | ~ spl1_91
    | ~ spl1_2
    | ~ spl1_12
    | ~ spl1_85 ),
    inference(avatar_split_clause,[],[f831,f825,f110,f66,f946,f942])).

fof(f66,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f110,plain,
    ( spl1_12
  <=> ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f825,plain,
    ( spl1_85
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_85])])).

fof(f831,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_2
    | ~ spl1_12
    | ~ spl1_85 ),
    inference(subsumption_resolution,[],[f830,f68])).

fof(f68,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f830,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12
    | ~ spl1_85 ),
    inference(superposition,[],[f111,f827])).

fof(f827,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_85 ),
    inference(avatar_component_clause,[],[f825])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f925,plain,
    ( spl1_24
    | ~ spl1_7
    | ~ spl1_38
    | ~ spl1_54
    | ~ spl1_87 ),
    inference(avatar_split_clause,[],[f875,f843,f533,f281,f89,f180])).

fof(f180,plain,
    ( spl1_24
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f281,plain,
    ( spl1_38
  <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).

fof(f533,plain,
    ( spl1_54
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_54])])).

fof(f843,plain,
    ( spl1_87
  <=> v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_87])])).

fof(f875,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_38
    | ~ spl1_54
    | ~ spl1_87 ),
    inference(forward_demodulation,[],[f854,f535])).

fof(f535,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_54 ),
    inference(avatar_component_clause,[],[f533])).

fof(f854,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_38
    | ~ spl1_87 ),
    inference(backward_demodulation,[],[f283,f847])).

fof(f847,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_7
    | ~ spl1_87 ),
    inference(resolution,[],[f845,f90])).

fof(f845,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_87 ),
    inference(avatar_component_clause,[],[f843])).

fof(f283,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_38 ),
    inference(avatar_component_clause,[],[f281])).

fof(f846,plain,
    ( spl1_87
    | ~ spl1_2
    | ~ spl1_12
    | ~ spl1_41
    | ~ spl1_86 ),
    inference(avatar_split_clause,[],[f841,f833,f317,f110,f66,f843])).

fof(f317,plain,
    ( spl1_41
  <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).

fof(f833,plain,
    ( spl1_86
  <=> k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_86])])).

fof(f841,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_2
    | ~ spl1_12
    | ~ spl1_41
    | ~ spl1_86 ),
    inference(subsumption_resolution,[],[f840,f318])).

fof(f318,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_41 ),
    inference(avatar_component_clause,[],[f317])).

fof(f840,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_2
    | ~ spl1_12
    | ~ spl1_86 ),
    inference(subsumption_resolution,[],[f838,f68])).

fof(f838,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_12
    | ~ spl1_86 ),
    inference(superposition,[],[f111,f835])).

fof(f835,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_86 ),
    inference(avatar_component_clause,[],[f833])).

fof(f836,plain,
    ( spl1_86
    | ~ spl1_52
    | ~ spl1_80
    | ~ spl1_84 ),
    inference(avatar_split_clause,[],[f823,f808,f779,f449,f833])).

fof(f449,plain,
    ( spl1_52
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).

fof(f779,plain,
    ( spl1_80
  <=> k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_80])])).

fof(f808,plain,
    ( spl1_84
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_84])])).

fof(f823,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_52
    | ~ spl1_80
    | ~ spl1_84 ),
    inference(forward_demodulation,[],[f817,f781])).

fof(f781,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_80 ),
    inference(avatar_component_clause,[],[f779])).

fof(f817,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_52
    | ~ spl1_84 ),
    inference(resolution,[],[f809,f450])).

fof(f450,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_52 ),
    inference(avatar_component_clause,[],[f449])).

fof(f809,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_84 ),
    inference(avatar_component_clause,[],[f808])).

fof(f828,plain,
    ( spl1_85
    | ~ spl1_1
    | ~ spl1_84 ),
    inference(avatar_split_clause,[],[f822,f808,f61,f825])).

fof(f822,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_84 ),
    inference(resolution,[],[f809,f63])).

fof(f810,plain,
    ( spl1_84
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_20
    | ~ spl1_73 ),
    inference(avatar_split_clause,[],[f805,f687,f153,f80,f75,f71,f808])).

fof(f71,plain,
    ( spl1_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f75,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f80,plain,
    ( spl1_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f687,plain,
    ( spl1_73
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_73])])).

fof(f805,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_20
    | ~ spl1_73 ),
    inference(forward_demodulation,[],[f804,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f804,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_20
    | ~ spl1_73 ),
    inference(subsumption_resolution,[],[f803,f155])).

fof(f803,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_73 ),
    inference(subsumption_resolution,[],[f801,f72])).

fof(f72,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f801,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_5
    | ~ spl1_73 ),
    inference(superposition,[],[f688,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f688,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_73 ),
    inference(avatar_component_clause,[],[f687])).

fof(f782,plain,
    ( spl1_80
    | ~ spl1_20
    | ~ spl1_54
    | ~ spl1_79 ),
    inference(avatar_split_clause,[],[f752,f736,f533,f153,f779])).

fof(f736,plain,
    ( spl1_79
  <=> ! [X15] :
        ( ~ v1_relat_1(X15)
        | k4_relat_1(k5_relat_1(sK0,X15)) = k5_relat_1(k4_relat_1(X15),k4_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_79])])).

fof(f752,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_20
    | ~ spl1_54
    | ~ spl1_79 ),
    inference(forward_demodulation,[],[f740,f535])).

fof(f740,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))
    | ~ spl1_20
    | ~ spl1_79 ),
    inference(resolution,[],[f737,f155])).

fof(f737,plain,
    ( ! [X15] :
        ( ~ v1_relat_1(X15)
        | k4_relat_1(k5_relat_1(sK0,X15)) = k5_relat_1(k4_relat_1(X15),k4_relat_1(sK0)) )
    | ~ spl1_79 ),
    inference(avatar_component_clause,[],[f736])).

fof(f738,plain,
    ( spl1_79
    | ~ spl1_1
    | ~ spl1_43 ),
    inference(avatar_split_clause,[],[f591,f334,f61,f736])).

fof(f334,plain,
    ( spl1_43
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).

fof(f591,plain,
    ( ! [X15] :
        ( ~ v1_relat_1(X15)
        | k4_relat_1(k5_relat_1(sK0,X15)) = k5_relat_1(k4_relat_1(X15),k4_relat_1(sK0)) )
    | ~ spl1_1
    | ~ spl1_43 ),
    inference(resolution,[],[f335,f63])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl1_43 ),
    inference(avatar_component_clause,[],[f334])).

fof(f689,plain,(
    spl1_73 ),
    inference(avatar_split_clause,[],[f50,f687])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f536,plain,
    ( spl1_54
    | ~ spl1_1
    | ~ spl1_28
    | ~ spl1_53 ),
    inference(avatar_split_clause,[],[f513,f488,f209,f61,f533])).

fof(f209,plain,
    ( spl1_28
  <=> ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f488,plain,
    ( spl1_53
  <=> ! [X15] :
        ( ~ v1_relat_1(X15)
        | k4_relat_1(k6_subset_1(sK0,X15)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X15)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_53])])).

fof(f513,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_28
    | ~ spl1_53 ),
    inference(forward_demodulation,[],[f512,f210])).

fof(f210,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1)
    | ~ spl1_28 ),
    inference(avatar_component_clause,[],[f209])).

fof(f512,plain,
    ( k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0))
    | ~ spl1_1
    | ~ spl1_28
    | ~ spl1_53 ),
    inference(forward_demodulation,[],[f505,f210])).

fof(f505,plain,
    ( k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_53 ),
    inference(resolution,[],[f489,f63])).

fof(f489,plain,
    ( ! [X15] :
        ( ~ v1_relat_1(X15)
        | k4_relat_1(k6_subset_1(sK0,X15)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X15)) )
    | ~ spl1_53 ),
    inference(avatar_component_clause,[],[f488])).

fof(f490,plain,
    ( spl1_53
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(avatar_split_clause,[],[f443,f245,f61,f488])).

fof(f245,plain,
    ( spl1_33
  <=> ! [X1,X0] :
        ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f443,plain,
    ( ! [X15] :
        ( ~ v1_relat_1(X15)
        | k4_relat_1(k6_subset_1(sK0,X15)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X15)) )
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(resolution,[],[f246,f63])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) )
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f245])).

fof(f456,plain,
    ( ~ spl1_1
    | ~ spl1_8
    | spl1_52 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_8
    | spl1_52 ),
    inference(subsumption_resolution,[],[f453,f63])).

fof(f453,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_8
    | spl1_52 ),
    inference(resolution,[],[f451,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl1_8
  <=> ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f451,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_52 ),
    inference(avatar_component_clause,[],[f449])).

fof(f336,plain,(
    spl1_43 ),
    inference(avatar_split_clause,[],[f49,f334])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f332,plain,
    ( ~ spl1_1
    | ~ spl1_20
    | ~ spl1_22
    | spl1_42 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_20
    | ~ spl1_22
    | spl1_42 ),
    inference(subsumption_resolution,[],[f330,f63])).

fof(f330,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_20
    | ~ spl1_22
    | spl1_42 ),
    inference(subsumption_resolution,[],[f328,f155])).

fof(f328,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_22
    | spl1_42 ),
    inference(resolution,[],[f322,f171])).

fof(f322,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_42 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl1_42
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).

fof(f327,plain,
    ( ~ spl1_42
    | ~ spl1_8
    | spl1_41 ),
    inference(avatar_split_clause,[],[f325,f317,f93,f321])).

fof(f325,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_8
    | spl1_41 ),
    inference(resolution,[],[f319,f94])).

fof(f319,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_41 ),
    inference(avatar_component_clause,[],[f317])).

fof(f284,plain,
    ( spl1_38
    | ~ spl1_20
    | ~ spl1_36 ),
    inference(avatar_split_clause,[],[f269,f265,f153,f281])).

fof(f265,plain,
    ( spl1_36
  <=> ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).

fof(f269,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_20
    | ~ spl1_36 ),
    inference(resolution,[],[f266,f155])).

fof(f266,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_36 ),
    inference(avatar_component_clause,[],[f265])).

fof(f267,plain,
    ( spl1_36
    | ~ spl1_1
    | ~ spl1_35 ),
    inference(avatar_split_clause,[],[f263,f255,f61,f265])).

fof(f255,plain,
    ( spl1_35
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f263,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_1
    | ~ spl1_35 ),
    inference(resolution,[],[f256,f63])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_35 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl1_35
    | ~ spl1_11
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f174,f170,f106,f255])).

fof(f106,plain,
    ( spl1_11
  <=> ! [X0] :
        ( k4_relat_1(k4_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_11
    | ~ spl1_22 ),
    inference(resolution,[],[f171,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k4_relat_1(X0)) = X0 )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f247,plain,(
    spl1_33 ),
    inference(avatar_split_clause,[],[f48,f245])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f211,plain,
    ( spl1_28
    | ~ spl1_7
    | ~ spl1_27 ),
    inference(avatar_split_clause,[],[f205,f201,f89,f209])).

fof(f201,plain,
    ( spl1_27
  <=> ! [X0] : v1_xboole_0(k6_subset_1(X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f205,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1)
    | ~ spl1_7
    | ~ spl1_27 ),
    inference(resolution,[],[f202,f90])).

fof(f202,plain,
    ( ! [X0] : v1_xboole_0(k6_subset_1(X0,X0))
    | ~ spl1_27 ),
    inference(avatar_component_clause,[],[f201])).

fof(f203,plain,
    ( spl1_27
    | ~ spl1_16
    | ~ spl1_26 ),
    inference(avatar_split_clause,[],[f199,f189,f133,f201])).

fof(f133,plain,
    ( spl1_16
  <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f189,plain,
    ( spl1_26
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
        | v1_xboole_0(k6_subset_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f199,plain,
    ( ! [X0] : v1_xboole_0(k6_subset_1(X0,X0))
    | ~ spl1_16
    | ~ spl1_26 ),
    inference(resolution,[],[f190,f134])).

fof(f134,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
        | v1_xboole_0(k6_subset_1(X0,X1)) )
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl1_26
    | ~ spl1_9
    | ~ spl1_21 ),
    inference(avatar_split_clause,[],[f173,f166,f97,f189])).

fof(f97,plain,
    ( spl1_9
  <=> ! [X1,X0] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f166,plain,
    ( spl1_21
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
        | v1_xboole_0(k6_subset_1(X0,X1)) )
    | ~ spl1_9
    | ~ spl1_21 ),
    inference(resolution,[],[f167,f98])).

fof(f98,plain,
    ( ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f166])).

fof(f183,plain,
    ( ~ spl1_23
    | ~ spl1_24 ),
    inference(avatar_split_clause,[],[f39,f180,f176])).

fof(f39,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f172,plain,(
    spl1_22 ),
    inference(avatar_split_clause,[],[f56,f170])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f168,plain,(
    spl1_21 ),
    inference(avatar_split_clause,[],[f55,f166])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f162,plain,
    ( ~ spl1_2
    | ~ spl1_6
    | spl1_20 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_6
    | spl1_20 ),
    inference(subsumption_resolution,[],[f160,f68])).

fof(f160,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_6
    | spl1_20 ),
    inference(resolution,[],[f154,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f154,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f135,plain,
    ( spl1_16
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f131,f114,f102,f133])).

fof(f102,plain,
    ( spl1_10
  <=> ! [X1,X0] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f114,plain,
    ( spl1_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f131,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(resolution,[],[f115,f103])).

fof(f103,plain,
    ( ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,(
    spl1_13 ),
    inference(avatar_split_clause,[],[f57,f114])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f112,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f51,f110])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f108,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f104,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f99,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f59,f97])).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f52,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f95,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f46,f93])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f91,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f87,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f44,f85])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f83,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f78,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f43,f71])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f69,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f64,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f38,f61])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (18598)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (18589)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (18603)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (18593)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (18591)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (18592)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (18594)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (18586)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (18601)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.51  % (18597)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (18600)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (18588)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.52  % (18599)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.53  % (18605)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.54  % (18596)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.54  % (18604)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.54  % (18587)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.56  % (18594)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f974,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f64,f69,f73,f78,f83,f87,f91,f95,f99,f104,f108,f112,f116,f135,f162,f168,f172,f183,f191,f203,f211,f247,f257,f267,f284,f327,f332,f336,f456,f490,f536,f689,f738,f782,f810,f828,f836,f846,f925,f949,f954,f964])).
% 0.20/0.56  fof(f964,plain,(
% 0.20/0.56    ~spl1_7 | spl1_23 | ~spl1_90),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f963])).
% 0.20/0.56  fof(f963,plain,(
% 0.20/0.56    $false | (~spl1_7 | spl1_23 | ~spl1_90)),
% 0.20/0.56    inference(subsumption_resolution,[],[f956,f178])).
% 0.20/0.56  fof(f178,plain,(
% 0.20/0.56    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_23),
% 0.20/0.56    inference(avatar_component_clause,[],[f176])).
% 0.20/0.56  fof(f176,plain,(
% 0.20/0.56    spl1_23 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.20/0.56  fof(f956,plain,(
% 0.20/0.56    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_7 | ~spl1_90)),
% 0.20/0.56    inference(resolution,[],[f944,f90])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f89])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    spl1_7 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.56  fof(f944,plain,(
% 0.20/0.56    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_90),
% 0.20/0.56    inference(avatar_component_clause,[],[f942])).
% 0.20/0.56  fof(f942,plain,(
% 0.20/0.56    spl1_90 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_90])])).
% 0.20/0.56  fof(f954,plain,(
% 0.20/0.56    ~spl1_1 | ~spl1_20 | ~spl1_22 | spl1_91),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f953])).
% 0.20/0.56  fof(f953,plain,(
% 0.20/0.56    $false | (~spl1_1 | ~spl1_20 | ~spl1_22 | spl1_91)),
% 0.20/0.56    inference(subsumption_resolution,[],[f952,f155])).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    v1_relat_1(k1_xboole_0) | ~spl1_20),
% 0.20/0.56    inference(avatar_component_clause,[],[f153])).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    spl1_20 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.20/0.56  fof(f952,plain,(
% 0.20/0.56    ~v1_relat_1(k1_xboole_0) | (~spl1_1 | ~spl1_22 | spl1_91)),
% 0.20/0.56    inference(subsumption_resolution,[],[f950,f63])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    v1_relat_1(sK0) | ~spl1_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    spl1_1 <=> v1_relat_1(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.56  fof(f950,plain,(
% 0.20/0.56    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | (~spl1_22 | spl1_91)),
% 0.20/0.56    inference(resolution,[],[f948,f171])).
% 0.20/0.56  fof(f171,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_22),
% 0.20/0.56    inference(avatar_component_clause,[],[f170])).
% 0.20/0.56  fof(f170,plain,(
% 0.20/0.56    spl1_22 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.20/0.56  fof(f948,plain,(
% 0.20/0.56    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_91),
% 0.20/0.56    inference(avatar_component_clause,[],[f946])).
% 0.20/0.56  fof(f946,plain,(
% 0.20/0.56    spl1_91 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_91])])).
% 0.20/0.56  fof(f949,plain,(
% 0.20/0.56    spl1_90 | ~spl1_91 | ~spl1_2 | ~spl1_12 | ~spl1_85),
% 0.20/0.56    inference(avatar_split_clause,[],[f831,f825,f110,f66,f946,f942])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.56  fof(f110,plain,(
% 0.20/0.56    spl1_12 <=> ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.56  fof(f825,plain,(
% 0.20/0.56    spl1_85 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_85])])).
% 0.20/0.56  fof(f831,plain,(
% 0.20/0.56    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_2 | ~spl1_12 | ~spl1_85)),
% 0.20/0.56    inference(subsumption_resolution,[],[f830,f68])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f66])).
% 0.20/0.56  fof(f830,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_12 | ~spl1_85)),
% 0.20/0.56    inference(superposition,[],[f111,f827])).
% 0.20/0.56  fof(f827,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_85),
% 0.20/0.56    inference(avatar_component_clause,[],[f825])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl1_12),
% 0.20/0.56    inference(avatar_component_clause,[],[f110])).
% 0.20/0.56  fof(f925,plain,(
% 0.20/0.56    spl1_24 | ~spl1_7 | ~spl1_38 | ~spl1_54 | ~spl1_87),
% 0.20/0.56    inference(avatar_split_clause,[],[f875,f843,f533,f281,f89,f180])).
% 0.20/0.56  fof(f180,plain,(
% 0.20/0.56    spl1_24 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 0.20/0.56  fof(f281,plain,(
% 0.20/0.56    spl1_38 <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).
% 0.20/0.56  fof(f533,plain,(
% 0.20/0.56    spl1_54 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_54])])).
% 0.20/0.56  fof(f843,plain,(
% 0.20/0.56    spl1_87 <=> v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_87])])).
% 0.20/0.56  fof(f875,plain,(
% 0.20/0.56    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_7 | ~spl1_38 | ~spl1_54 | ~spl1_87)),
% 0.20/0.56    inference(forward_demodulation,[],[f854,f535])).
% 0.20/0.56  fof(f535,plain,(
% 0.20/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_54),
% 0.20/0.56    inference(avatar_component_clause,[],[f533])).
% 0.20/0.56  fof(f854,plain,(
% 0.20/0.56    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl1_7 | ~spl1_38 | ~spl1_87)),
% 0.20/0.56    inference(backward_demodulation,[],[f283,f847])).
% 0.20/0.56  fof(f847,plain,(
% 0.20/0.56    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_7 | ~spl1_87)),
% 0.20/0.56    inference(resolution,[],[f845,f90])).
% 0.20/0.56  fof(f845,plain,(
% 0.20/0.56    v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_87),
% 0.20/0.56    inference(avatar_component_clause,[],[f843])).
% 0.20/0.56  fof(f283,plain,(
% 0.20/0.56    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_38),
% 0.20/0.56    inference(avatar_component_clause,[],[f281])).
% 0.20/0.56  fof(f846,plain,(
% 0.20/0.56    spl1_87 | ~spl1_2 | ~spl1_12 | ~spl1_41 | ~spl1_86),
% 0.20/0.56    inference(avatar_split_clause,[],[f841,f833,f317,f110,f66,f843])).
% 0.20/0.56  fof(f317,plain,(
% 0.20/0.56    spl1_41 <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).
% 0.20/0.56  fof(f833,plain,(
% 0.20/0.56    spl1_86 <=> k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_86])])).
% 0.20/0.56  fof(f841,plain,(
% 0.20/0.56    v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_2 | ~spl1_12 | ~spl1_41 | ~spl1_86)),
% 0.20/0.56    inference(subsumption_resolution,[],[f840,f318])).
% 0.20/0.56  fof(f318,plain,(
% 0.20/0.56    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_41),
% 0.20/0.56    inference(avatar_component_clause,[],[f317])).
% 0.20/0.56  fof(f840,plain,(
% 0.20/0.56    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_2 | ~spl1_12 | ~spl1_86)),
% 0.20/0.56    inference(subsumption_resolution,[],[f838,f68])).
% 0.20/0.56  fof(f838,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_12 | ~spl1_86)),
% 0.20/0.56    inference(superposition,[],[f111,f835])).
% 0.20/0.56  fof(f835,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_86),
% 0.20/0.56    inference(avatar_component_clause,[],[f833])).
% 0.20/0.56  fof(f836,plain,(
% 0.20/0.56    spl1_86 | ~spl1_52 | ~spl1_80 | ~spl1_84),
% 0.20/0.56    inference(avatar_split_clause,[],[f823,f808,f779,f449,f833])).
% 0.20/0.56  fof(f449,plain,(
% 0.20/0.56    spl1_52 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).
% 0.20/0.56  fof(f779,plain,(
% 0.20/0.56    spl1_80 <=> k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_80])])).
% 0.20/0.56  fof(f808,plain,(
% 0.20/0.56    spl1_84 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_84])])).
% 0.20/0.56  fof(f823,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_52 | ~spl1_80 | ~spl1_84)),
% 0.20/0.56    inference(forward_demodulation,[],[f817,f781])).
% 0.20/0.56  fof(f781,plain,(
% 0.20/0.56    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl1_80),
% 0.20/0.56    inference(avatar_component_clause,[],[f779])).
% 0.20/0.56  fof(f817,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | (~spl1_52 | ~spl1_84)),
% 0.20/0.56    inference(resolution,[],[f809,f450])).
% 0.20/0.56  fof(f450,plain,(
% 0.20/0.56    v1_relat_1(k4_relat_1(sK0)) | ~spl1_52),
% 0.20/0.56    inference(avatar_component_clause,[],[f449])).
% 0.20/0.56  fof(f809,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_84),
% 0.20/0.56    inference(avatar_component_clause,[],[f808])).
% 0.20/0.56  fof(f828,plain,(
% 0.20/0.56    spl1_85 | ~spl1_1 | ~spl1_84),
% 0.20/0.56    inference(avatar_split_clause,[],[f822,f808,f61,f825])).
% 0.20/0.56  fof(f822,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_84)),
% 0.20/0.56    inference(resolution,[],[f809,f63])).
% 0.20/0.56  fof(f810,plain,(
% 0.20/0.56    spl1_84 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_20 | ~spl1_73),
% 0.20/0.56    inference(avatar_split_clause,[],[f805,f687,f153,f80,f75,f71,f808])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    spl1_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    spl1_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.56  fof(f687,plain,(
% 0.20/0.56    spl1_73 <=> ! [X1,X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_73])])).
% 0.20/0.56  fof(f805,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_20 | ~spl1_73)),
% 0.20/0.56    inference(forward_demodulation,[],[f804,f77])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f75])).
% 0.20/0.56  fof(f804,plain,(
% 0.20/0.56    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_5 | ~spl1_20 | ~spl1_73)),
% 0.20/0.56    inference(subsumption_resolution,[],[f803,f155])).
% 0.20/0.56  fof(f803,plain,(
% 0.20/0.56    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_5 | ~spl1_73)),
% 0.20/0.56    inference(subsumption_resolution,[],[f801,f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f71])).
% 0.20/0.56  fof(f801,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_5 | ~spl1_73)),
% 0.20/0.56    inference(superposition,[],[f688,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f80])).
% 0.20/0.56  fof(f688,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_73),
% 0.20/0.56    inference(avatar_component_clause,[],[f687])).
% 0.20/0.56  fof(f782,plain,(
% 0.20/0.56    spl1_80 | ~spl1_20 | ~spl1_54 | ~spl1_79),
% 0.20/0.56    inference(avatar_split_clause,[],[f752,f736,f533,f153,f779])).
% 0.20/0.56  fof(f736,plain,(
% 0.20/0.56    spl1_79 <=> ! [X15] : (~v1_relat_1(X15) | k4_relat_1(k5_relat_1(sK0,X15)) = k5_relat_1(k4_relat_1(X15),k4_relat_1(sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_79])])).
% 0.20/0.56  fof(f752,plain,(
% 0.20/0.56    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | (~spl1_20 | ~spl1_54 | ~spl1_79)),
% 0.20/0.56    inference(forward_demodulation,[],[f740,f535])).
% 0.20/0.56  fof(f740,plain,(
% 0.20/0.56    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) | (~spl1_20 | ~spl1_79)),
% 0.20/0.56    inference(resolution,[],[f737,f155])).
% 0.20/0.56  fof(f737,plain,(
% 0.20/0.56    ( ! [X15] : (~v1_relat_1(X15) | k4_relat_1(k5_relat_1(sK0,X15)) = k5_relat_1(k4_relat_1(X15),k4_relat_1(sK0))) ) | ~spl1_79),
% 0.20/0.56    inference(avatar_component_clause,[],[f736])).
% 0.20/0.56  fof(f738,plain,(
% 0.20/0.56    spl1_79 | ~spl1_1 | ~spl1_43),
% 0.20/0.56    inference(avatar_split_clause,[],[f591,f334,f61,f736])).
% 0.20/0.56  fof(f334,plain,(
% 0.20/0.56    spl1_43 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).
% 0.20/0.56  fof(f591,plain,(
% 0.20/0.56    ( ! [X15] : (~v1_relat_1(X15) | k4_relat_1(k5_relat_1(sK0,X15)) = k5_relat_1(k4_relat_1(X15),k4_relat_1(sK0))) ) | (~spl1_1 | ~spl1_43)),
% 0.20/0.56    inference(resolution,[],[f335,f63])).
% 0.20/0.56  fof(f335,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl1_43),
% 0.20/0.56    inference(avatar_component_clause,[],[f334])).
% 0.20/0.56  fof(f689,plain,(
% 0.20/0.56    spl1_73),
% 0.20/0.56    inference(avatar_split_clause,[],[f50,f687])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.56  fof(f536,plain,(
% 0.20/0.56    spl1_54 | ~spl1_1 | ~spl1_28 | ~spl1_53),
% 0.20/0.56    inference(avatar_split_clause,[],[f513,f488,f209,f61,f533])).
% 0.20/0.56  fof(f209,plain,(
% 0.20/0.56    spl1_28 <=> ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.20/0.56  fof(f488,plain,(
% 0.20/0.56    spl1_53 <=> ! [X15] : (~v1_relat_1(X15) | k4_relat_1(k6_subset_1(sK0,X15)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X15)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_53])])).
% 0.20/0.56  fof(f513,plain,(
% 0.20/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_1 | ~spl1_28 | ~spl1_53)),
% 0.20/0.56    inference(forward_demodulation,[],[f512,f210])).
% 0.20/0.56  fof(f210,plain,(
% 0.20/0.56    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) ) | ~spl1_28),
% 0.20/0.56    inference(avatar_component_clause,[],[f209])).
% 0.20/0.56  fof(f512,plain,(
% 0.20/0.56    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0)) | (~spl1_1 | ~spl1_28 | ~spl1_53)),
% 0.20/0.56    inference(forward_demodulation,[],[f505,f210])).
% 0.20/0.56  fof(f505,plain,(
% 0.20/0.56    k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) | (~spl1_1 | ~spl1_53)),
% 0.20/0.56    inference(resolution,[],[f489,f63])).
% 0.20/0.56  fof(f489,plain,(
% 0.20/0.56    ( ! [X15] : (~v1_relat_1(X15) | k4_relat_1(k6_subset_1(sK0,X15)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X15))) ) | ~spl1_53),
% 0.20/0.56    inference(avatar_component_clause,[],[f488])).
% 0.20/0.56  fof(f490,plain,(
% 0.20/0.56    spl1_53 | ~spl1_1 | ~spl1_33),
% 0.20/0.56    inference(avatar_split_clause,[],[f443,f245,f61,f488])).
% 0.20/0.56  fof(f245,plain,(
% 0.20/0.56    spl1_33 <=> ! [X1,X0] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.20/0.56  fof(f443,plain,(
% 0.20/0.56    ( ! [X15] : (~v1_relat_1(X15) | k4_relat_1(k6_subset_1(sK0,X15)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X15))) ) | (~spl1_1 | ~spl1_33)),
% 0.20/0.56    inference(resolution,[],[f246,f63])).
% 0.20/0.56  fof(f246,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))) ) | ~spl1_33),
% 0.20/0.56    inference(avatar_component_clause,[],[f245])).
% 0.20/0.56  fof(f456,plain,(
% 0.20/0.56    ~spl1_1 | ~spl1_8 | spl1_52),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f455])).
% 0.20/0.56  fof(f455,plain,(
% 0.20/0.56    $false | (~spl1_1 | ~spl1_8 | spl1_52)),
% 0.20/0.56    inference(subsumption_resolution,[],[f453,f63])).
% 0.20/0.56  fof(f453,plain,(
% 0.20/0.56    ~v1_relat_1(sK0) | (~spl1_8 | spl1_52)),
% 0.20/0.56    inference(resolution,[],[f451,f94])).
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    spl1_8 <=> ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.56  fof(f451,plain,(
% 0.20/0.56    ~v1_relat_1(k4_relat_1(sK0)) | spl1_52),
% 0.20/0.56    inference(avatar_component_clause,[],[f449])).
% 0.20/0.56  fof(f336,plain,(
% 0.20/0.56    spl1_43),
% 0.20/0.56    inference(avatar_split_clause,[],[f49,f334])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.56  fof(f332,plain,(
% 0.20/0.56    ~spl1_1 | ~spl1_20 | ~spl1_22 | spl1_42),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f331])).
% 0.20/0.56  fof(f331,plain,(
% 0.20/0.56    $false | (~spl1_1 | ~spl1_20 | ~spl1_22 | spl1_42)),
% 0.20/0.56    inference(subsumption_resolution,[],[f330,f63])).
% 0.20/0.56  fof(f330,plain,(
% 0.20/0.56    ~v1_relat_1(sK0) | (~spl1_20 | ~spl1_22 | spl1_42)),
% 0.20/0.56    inference(subsumption_resolution,[],[f328,f155])).
% 0.20/0.56  fof(f328,plain,(
% 0.20/0.56    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | (~spl1_22 | spl1_42)),
% 0.20/0.56    inference(resolution,[],[f322,f171])).
% 0.20/0.56  fof(f322,plain,(
% 0.20/0.56    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_42),
% 0.20/0.56    inference(avatar_component_clause,[],[f321])).
% 0.20/0.56  fof(f321,plain,(
% 0.20/0.56    spl1_42 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).
% 0.20/0.56  fof(f327,plain,(
% 0.20/0.56    ~spl1_42 | ~spl1_8 | spl1_41),
% 0.20/0.56    inference(avatar_split_clause,[],[f325,f317,f93,f321])).
% 0.20/0.56  fof(f325,plain,(
% 0.20/0.56    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_8 | spl1_41)),
% 0.20/0.56    inference(resolution,[],[f319,f94])).
% 0.20/0.56  fof(f319,plain,(
% 0.20/0.56    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | spl1_41),
% 0.20/0.56    inference(avatar_component_clause,[],[f317])).
% 0.20/0.56  fof(f284,plain,(
% 0.20/0.56    spl1_38 | ~spl1_20 | ~spl1_36),
% 0.20/0.56    inference(avatar_split_clause,[],[f269,f265,f153,f281])).
% 0.20/0.56  fof(f265,plain,(
% 0.20/0.56    spl1_36 <=> ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).
% 0.20/0.56  fof(f269,plain,(
% 0.20/0.56    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_20 | ~spl1_36)),
% 0.20/0.56    inference(resolution,[],[f266,f155])).
% 0.20/0.56  fof(f266,plain,(
% 0.20/0.56    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | ~spl1_36),
% 0.20/0.56    inference(avatar_component_clause,[],[f265])).
% 0.20/0.56  fof(f267,plain,(
% 0.20/0.56    spl1_36 | ~spl1_1 | ~spl1_35),
% 0.20/0.56    inference(avatar_split_clause,[],[f263,f255,f61,f265])).
% 0.20/0.56  fof(f255,plain,(
% 0.20/0.56    spl1_35 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.20/0.56  fof(f263,plain,(
% 0.20/0.56    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | (~spl1_1 | ~spl1_35)),
% 0.20/0.56    inference(resolution,[],[f256,f63])).
% 0.20/0.56  fof(f256,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | ~spl1_35),
% 0.20/0.56    inference(avatar_component_clause,[],[f255])).
% 0.20/0.56  fof(f257,plain,(
% 0.20/0.56    spl1_35 | ~spl1_11 | ~spl1_22),
% 0.20/0.56    inference(avatar_split_clause,[],[f174,f170,f106,f255])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    spl1_11 <=> ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.56  fof(f174,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | (~spl1_11 | ~spl1_22)),
% 0.20/0.56    inference(resolution,[],[f171,f107])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) ) | ~spl1_11),
% 0.20/0.56    inference(avatar_component_clause,[],[f106])).
% 0.20/0.56  fof(f247,plain,(
% 0.20/0.56    spl1_33),
% 0.20/0.56    inference(avatar_split_clause,[],[f48,f245])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 0.20/0.56  fof(f211,plain,(
% 0.20/0.56    spl1_28 | ~spl1_7 | ~spl1_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f205,f201,f89,f209])).
% 0.20/0.56  fof(f201,plain,(
% 0.20/0.56    spl1_27 <=> ! [X0] : v1_xboole_0(k6_subset_1(X0,X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.20/0.56  fof(f205,plain,(
% 0.20/0.56    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) ) | (~spl1_7 | ~spl1_27)),
% 0.20/0.56    inference(resolution,[],[f202,f90])).
% 0.20/0.56  fof(f202,plain,(
% 0.20/0.56    ( ! [X0] : (v1_xboole_0(k6_subset_1(X0,X0))) ) | ~spl1_27),
% 0.20/0.56    inference(avatar_component_clause,[],[f201])).
% 0.20/0.56  fof(f203,plain,(
% 0.20/0.56    spl1_27 | ~spl1_16 | ~spl1_26),
% 0.20/0.56    inference(avatar_split_clause,[],[f199,f189,f133,f201])).
% 0.20/0.56  fof(f133,plain,(
% 0.20/0.56    spl1_16 <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.56  fof(f189,plain,(
% 0.20/0.56    spl1_26 <=> ! [X1,X0] : (~r1_tarski(k6_subset_1(X0,X1),X1) | v1_xboole_0(k6_subset_1(X0,X1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.20/0.56  fof(f199,plain,(
% 0.20/0.56    ( ! [X0] : (v1_xboole_0(k6_subset_1(X0,X0))) ) | (~spl1_16 | ~spl1_26)),
% 0.20/0.56    inference(resolution,[],[f190,f134])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | ~spl1_16),
% 0.20/0.56    inference(avatar_component_clause,[],[f133])).
% 0.20/0.56  fof(f190,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X1) | v1_xboole_0(k6_subset_1(X0,X1))) ) | ~spl1_26),
% 0.20/0.56    inference(avatar_component_clause,[],[f189])).
% 0.20/0.56  fof(f191,plain,(
% 0.20/0.56    spl1_26 | ~spl1_9 | ~spl1_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f173,f166,f97,f189])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    spl1_9 <=> ! [X1,X0] : r1_xboole_0(k6_subset_1(X0,X1),X1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.56  fof(f166,plain,(
% 0.20/0.56    spl1_21 <=> ! [X1,X0] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.20/0.56  fof(f173,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X1) | v1_xboole_0(k6_subset_1(X0,X1))) ) | (~spl1_9 | ~spl1_21)),
% 0.20/0.56    inference(resolution,[],[f167,f98])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) ) | ~spl1_9),
% 0.20/0.56    inference(avatar_component_clause,[],[f97])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) ) | ~spl1_21),
% 0.20/0.56    inference(avatar_component_clause,[],[f166])).
% 0.20/0.56  fof(f183,plain,(
% 0.20/0.56    ~spl1_23 | ~spl1_24),
% 0.20/0.56    inference(avatar_split_clause,[],[f39,f180,f176])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.56    inference(negated_conjecture,[],[f18])).
% 0.20/0.56  fof(f18,conjecture,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.56  fof(f172,plain,(
% 0.20/0.56    spl1_22),
% 0.20/0.56    inference(avatar_split_clause,[],[f56,f170])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.56  fof(f168,plain,(
% 0.20/0.56    spl1_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f55,f166])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.56    inference(flattening,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    ~spl1_2 | ~spl1_6 | spl1_20),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f161])).
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    $false | (~spl1_2 | ~spl1_6 | spl1_20)),
% 0.20/0.56    inference(subsumption_resolution,[],[f160,f68])).
% 0.20/0.56  fof(f160,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl1_6 | spl1_20)),
% 0.20/0.56    inference(resolution,[],[f154,f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.56  fof(f154,plain,(
% 0.20/0.56    ~v1_relat_1(k1_xboole_0) | spl1_20),
% 0.20/0.56    inference(avatar_component_clause,[],[f153])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    spl1_16 | ~spl1_10 | ~spl1_13),
% 0.20/0.56    inference(avatar_split_clause,[],[f131,f114,f102,f133])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    spl1_10 <=> ! [X1,X0] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.56  fof(f114,plain,(
% 0.20/0.56    spl1_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.56  fof(f131,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | (~spl1_10 | ~spl1_13)),
% 0.20/0.56    inference(resolution,[],[f115,f103])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) ) | ~spl1_10),
% 0.20/0.56    inference(avatar_component_clause,[],[f102])).
% 0.20/0.56  fof(f115,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl1_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f114])).
% 0.20/0.56  fof(f116,plain,(
% 0.20/0.56    spl1_13),
% 0.20/0.56    inference(avatar_split_clause,[],[f57,f114])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f112,plain,(
% 0.20/0.56    spl1_12),
% 0.20/0.56    inference(avatar_split_clause,[],[f51,f110])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.56  fof(f108,plain,(
% 0.20/0.56    spl1_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f47,f106])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    spl1_10),
% 0.20/0.56    inference(avatar_split_clause,[],[f53,f102])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    spl1_9),
% 0.20/0.56    inference(avatar_split_clause,[],[f59,f97])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f52,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    spl1_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f46,f93])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    spl1_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f45,f89])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    spl1_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f44,f85])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    spl1_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f42,f80])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,axiom,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    spl1_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f41,f75])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    spl1_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f43,f71])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    spl1_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f40,f66])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    spl1_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f38,f61])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    v1_relat_1(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (18594)------------------------------
% 0.20/0.56  % (18594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18594)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (18594)Memory used [KB]: 6780
% 0.20/0.56  % (18594)Time elapsed: 0.107 s
% 0.20/0.56  % (18594)------------------------------
% 0.20/0.56  % (18594)------------------------------
% 0.20/0.57  % (18578)Success in time 0.21 s
%------------------------------------------------------------------------------
