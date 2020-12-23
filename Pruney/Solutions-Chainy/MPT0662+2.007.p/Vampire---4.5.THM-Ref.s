%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:12 EST 2020

% Result     : Theorem 4.63s
% Output     : Refutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  442 (3095 expanded)
%              Number of leaves         :  110 (1124 expanded)
%              Depth                    :   17
%              Number of atoms          : 1243 (10745 expanded)
%              Number of equality atoms :  110 (2481 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6687,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f119,f125,f141,f161,f168,f176,f191,f214,f232,f243,f263,f268,f273,f278,f312,f329,f340,f345,f350,f355,f430,f510,f541,f572,f577,f582,f654,f659,f664,f669,f805,f810,f815,f820,f1451,f1464,f1469,f1611,f1808,f1813,f1818,f1823,f2049,f2070,f2075,f2080,f2085,f2215,f2220,f2534,f2784,f2789,f2794,f2799,f2804,f2809,f2814,f2819,f2975,f2980,f3012,f3017,f3022,f3399,f3891,f3896,f3901,f3933,f4249,f4257,f4428,f4433,f4677,f4682,f5317,f5322,f5327,f5332,f5337,f5344,f5351,f5356,f5361,f5366,f5371,f5376,f5381,f5386,f5391,f5663,f6479,f6616,f6686])).

fof(f6686,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_73 ),
    inference(avatar_contradiction_clause,[],[f6685])).

fof(f6685,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f6684,f118])).

fof(f118,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f6684,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f6603,f91])).

fof(f91,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_4
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f6603,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_73 ),
    inference(superposition,[],[f1801,f4248])).

fof(f4248,plain,
    ( sK0 = k1_funct_1(k6_relat_1(sK1),sK0)
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f4246])).

fof(f4246,plain,
    ( spl7_73
  <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f1801,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
        | ~ r2_hidden(X2,X1) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f1800,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1800,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
        | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f1799,f93])).

fof(f93,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f76,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f76,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1799,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2))
        | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f1795,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f1795,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2))
        | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f394,f46])).

fof(f46,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f394,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f388,f76])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f58,f81])).

fof(f81,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f6616,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_73 ),
    inference(avatar_contradiction_clause,[],[f6615])).

fof(f6615,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f6614,f91])).

fof(f6614,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f6554,f4248])).

fof(f6554,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f118,f1801])).

fof(f6479,plain,
    ( spl7_95
    | ~ spl7_81 ),
    inference(avatar_split_clause,[],[f6424,f5324,f6476])).

fof(f6476,plain,
    ( spl7_95
  <=> r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f5324,plain,
    ( spl7_81
  <=> r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f6424,plain,
    ( r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1)
    | ~ spl7_81 ),
    inference(unit_resulting_resolution,[],[f5326,f112])).

fof(f112,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k3_xboole_0(X3,X4)) ) ),
    inference(forward_demodulation,[],[f111,f47])).

fof(f111,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k3_xboole_0(X3,X4))
      | r2_hidden(X2,k1_relat_1(k6_relat_1(X3))) ) ),
    inference(forward_demodulation,[],[f109,f103])).

fof(f103,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X0,X1) ),
    inference(forward_demodulation,[],[f98,f47])).

fof(f98,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f109,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))
      | r2_hidden(X2,k1_relat_1(k6_relat_1(X3))) ) ),
    inference(resolution,[],[f64,f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f5326,plain,
    ( r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1))
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f5324])).

fof(f5663,plain,
    ( spl7_94
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f1954,f1815,f5660])).

fof(f5660,plain,
    ( spl7_94
  <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f1815,plain,
    ( spl7_45
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1954,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),sK0),sK1)
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f1817,f285])).

fof(f285,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4)
      | ~ r2_hidden(X2,k3_xboole_0(X4,X3)) ) ),
    inference(forward_demodulation,[],[f284,f103])).

fof(f284,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X4),X3)))
      | r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4) ) ),
    inference(forward_demodulation,[],[f283,f94])).

fof(f94,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f45,f55])).

fof(f283,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))))
      | r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4) ) ),
    inference(subsumption_resolution,[],[f280,f45])).

fof(f280,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))))
      | r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(f1817,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f1815])).

fof(f5391,plain,
    ( spl7_93
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f747,f84,f5388])).

fof(f5388,plain,
    ( spl7_93
  <=> sK0 = k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f84,plain,
    ( spl7_3
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f747,plain,
    ( sK0 = k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0))
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f86,f251])).

fof(f251,plain,(
    ! [X2,X1] :
      ( k1_funct_1(k6_relat_1(X2),sK5(k6_relat_1(X2),X1)) = X1
      | ~ r2_hidden(X1,X2) ) ),
    inference(forward_demodulation,[],[f250,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f250,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k6_relat_1(X2)))
      | k1_funct_1(k6_relat_1(X2),sK5(k6_relat_1(X2),X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f246,f45])).

fof(f246,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k6_relat_1(X2)))
      | k1_funct_1(k6_relat_1(X2),sK5(k6_relat_1(X2),X1)) = X1
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f71,f46])).

fof(f71,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f86,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f5386,plain,
    ( spl7_92
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f1049,f229,f122,f74,f5383])).

fof(f5383,plain,
    ( spl7_92
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(k1_relat_1(sK2),sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f122,plain,
    ( spl7_6
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f229,plain,
    ( spl7_13
  <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f1049,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(k1_relat_1(sK2),sK0)))))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f994,f97])).

fof(f97,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f76,f56])).

fof(f994,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),k2_relat_1(sK6(k1_relat_1(sK2),sK0))))
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f124,f863,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(forward_demodulation,[],[f183,f47])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f181,f45])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f65,f103])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f863,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(sK6(k1_relat_1(sK2),X0)))
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f844,f238])).

fof(f238,plain,
    ( ! [X0] : k1_funct_1(sK6(k1_relat_1(sK2),X0),sK5(k6_relat_1(k1_relat_1(sK2)),sK0)) = X0
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f231,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f231,plain,
    ( r2_hidden(sK5(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f229])).

fof(f844,plain,
    ( ! [X0] : r2_hidden(k1_funct_1(sK6(k1_relat_1(sK2),X0),sK5(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK6(k1_relat_1(sK2),X0)))
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f231,f136])).

fof(f136,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k1_funct_1(sK6(X4,X5),X3),k2_relat_1(sK6(X4,X5)))
      | ~ r2_hidden(X3,X4) ) ),
    inference(forward_demodulation,[],[f135,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f135,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK6(X4,X5)))
      | r2_hidden(k1_funct_1(sK6(X4,X5),X3),k2_relat_1(sK6(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f130,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f130,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK6(X4,X5)))
      | r2_hidden(k1_funct_1(sK6(X4,X5),X3),k2_relat_1(sK6(X4,X5)))
      | ~ v1_relat_1(sK6(X4,X5)) ) ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f124,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f5381,plain,
    ( spl7_91
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f1025,f229,f122,f5378])).

fof(f5378,plain,
    ( spl7_91
  <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f1025,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),k1_relat_1(sK2)))
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f124,f863,f184])).

fof(f5376,plain,
    ( spl7_90
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f798,f666,f211,f5373])).

fof(f5373,plain,
    ( spl7_90
  <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f211,plain,
    ( spl7_12
  <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f666,plain,
    ( spl7_34
  <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f798,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f213,f668,f184])).

fof(f668,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f666])).

fof(f213,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK0),sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f211])).

fof(f5371,plain,
    ( spl7_89
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f796,f666,f211,f5368])).

fof(f5368,plain,
    ( spl7_89
  <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f796,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f213,f668,f184])).

fof(f5366,plain,
    ( spl7_88
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f725,f656,f116,f5363])).

fof(f5363,plain,
    ( spl7_88
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f656,plain,
    ( spl7_32
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f725,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1))
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f118,f658,f184])).

fof(f658,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f656])).

fof(f5361,plain,
    ( spl7_87
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f712,f656,f116,f5358])).

fof(f5358,plain,
    ( spl7_87
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f712,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1)))))
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f118,f658,f184])).

fof(f5356,plain,
    ( spl7_86
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f691,f651,f116,f5353])).

fof(f5353,plain,
    ( spl7_86
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f651,plain,
    ( spl7_31
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f691,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1),sK1))
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f118,f653,f184])).

fof(f653,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f651])).

fof(f5351,plain,
    ( spl7_85
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f679,f651,f116,f5348])).

fof(f5348,plain,
    ( spl7_85
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f679,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1)))
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f118,f653,f184])).

fof(f5344,plain,
    ( spl7_84
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f561,f538,f507,f5341])).

fof(f5341,plain,
    ( spl7_84
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k3_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f507,plain,
    ( spl7_26
  <=> r2_hidden(sK0,k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f538,plain,
    ( spl7_27
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f561,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k3_xboole_0(sK1,sK1)))
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f509,f540,f184])).

fof(f540,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f538])).

fof(f509,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f507])).

fof(f5337,plain,
    ( spl7_83
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f552,f538,f507,f5334])).

fof(f5334,plain,
    ( spl7_83
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f552,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k1_relat_1(sK2))))
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f509,f540,f184])).

fof(f5332,plain,
    ( spl7_82
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f532,f507,f5329])).

fof(f5329,plain,
    ( spl7_82
  <=> r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f532,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f509,f134])).

fof(f134,plain,(
    ! [X2,X1] :
      ( r2_hidden(k1_funct_1(k6_relat_1(X2),X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(forward_demodulation,[],[f133,f48])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(k6_relat_1(X2),X1),k2_relat_1(k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f132,f47])).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k6_relat_1(X2)))
      | r2_hidden(k1_funct_1(k6_relat_1(X2),X1),k2_relat_1(k6_relat_1(X2))) ) ),
    inference(subsumption_resolution,[],[f129,f45])).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k6_relat_1(X2)))
      | r2_hidden(k1_funct_1(k6_relat_1(X2),X1),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f70,f46])).

fof(f5327,plain,
    ( spl7_81
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f530,f507,f5324])).

fof(f530,plain,
    ( r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f509,f154])).

fof(f154,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK5(k6_relat_1(X2),X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(forward_demodulation,[],[f153,f47])).

fof(f153,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(sK5(k6_relat_1(X2),X1),k1_relat_1(k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f152,f48])).

fof(f152,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k6_relat_1(X2)))
      | r2_hidden(sK5(k6_relat_1(X2),X1),k1_relat_1(k6_relat_1(X2))) ) ),
    inference(subsumption_resolution,[],[f149,f45])).

fof(f149,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k6_relat_1(X2)))
      | r2_hidden(sK5(k6_relat_1(X2),X1),k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f72,f46])).

fof(f72,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5322,plain,
    ( spl7_80
    | ~ spl7_3
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f522,f507,f84,f5319])).

fof(f5319,plain,
    ( spl7_80
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f522,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl7_3
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f86,f509,f184])).

fof(f5317,plain,
    ( spl7_79
    | ~ spl7_3
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f514,f507,f84,f5314])).

fof(f5314,plain,
    ( spl7_79
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k3_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f514,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k3_xboole_0(sK1,sK1)))
    | ~ spl7_3
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f86,f509,f184])).

fof(f4682,plain,
    ( spl7_78
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f478,f326,f116,f4679])).

fof(f4679,plain,
    ( spl7_78
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f326,plain,
    ( spl7_20
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f478,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))))))
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f328,f118,f184])).

fof(f328,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f326])).

fof(f4677,plain,
    ( spl7_77
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f472,f326,f116,f4674])).

fof(f4674,plain,
    ( spl7_77
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f472,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),sK1))
    | ~ spl7_5
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f118,f328,f184])).

fof(f4433,plain,
    ( spl7_76
    | ~ spl7_1
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f3903,f3396,f74,f4430])).

fof(f4430,plain,
    ( spl7_76
  <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f3396,plain,
    ( spl7_68
  <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f3903,plain,
    ( r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f76,f3398,f64])).

fof(f3398,plain,
    ( r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f3396])).

fof(f4428,plain,
    ( spl7_75
    | ~ spl7_1
    | ~ spl7_67 ),
    inference(avatar_split_clause,[],[f3796,f3019,f74,f4425])).

fof(f4425,plain,
    ( spl7_75
  <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f3019,plain,
    ( spl7_67
  <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f3796,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f76,f3021,f64])).

fof(f3021,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f3019])).

fof(f4257,plain,
    ( spl7_74
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f442,f188,f122,f4254])).

fof(f4254,plain,
    ( spl7_74
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f188,plain,
    ( spl7_11
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f442,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),k1_relat_1(sK2)))
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f124,f190,f184])).

fof(f190,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f188])).

fof(f4249,plain,
    ( spl7_73
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f3982,f3893,f4246])).

fof(f3893,plain,
    ( spl7_70
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k2_relat_1(sK6(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f3982,plain,
    ( sK0 = k1_funct_1(k6_relat_1(sK1),sK0)
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f3895,f1606])).

fof(f1606,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_relat_1(sK6(X3,X4)))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f1602,f156])).

fof(f156,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK5(sK6(X4,X5),X3),X4)
      | ~ r2_hidden(X3,k2_relat_1(sK6(X4,X5))) ) ),
    inference(forward_demodulation,[],[f155,f61])).

fof(f155,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK6(X4,X5)))
      | r2_hidden(sK5(sK6(X4,X5),X3),k1_relat_1(sK6(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f150,f59])).

fof(f150,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK6(X4,X5)))
      | r2_hidden(sK5(sK6(X4,X5),X3),k1_relat_1(sK6(X4,X5)))
      | ~ v1_relat_1(sK6(X4,X5)) ) ),
    inference(resolution,[],[f72,f60])).

fof(f1602,plain,(
    ! [X4,X5,X3] :
      ( X4 = X5
      | ~ r2_hidden(X5,k2_relat_1(sK6(X3,X4)))
      | ~ r2_hidden(sK5(sK6(X3,X4),X5),X3) ) ),
    inference(superposition,[],[f252,f62])).

fof(f252,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(sK6(X4,X5),sK5(sK6(X4,X5),X3)) = X3
      | ~ r2_hidden(X3,k2_relat_1(sK6(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f247,f59])).

fof(f247,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK6(X4,X5)))
      | k1_funct_1(sK6(X4,X5),sK5(sK6(X4,X5),X3)) = X3
      | ~ v1_relat_1(sK6(X4,X5)) ) ),
    inference(resolution,[],[f71,f60])).

fof(f3895,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k2_relat_1(sK6(sK1,sK0)))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f3893])).

fof(f3933,plain,
    ( spl7_72
    | ~ spl7_1
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f3904,f3396,f74,f3930])).

fof(f3930,plain,
    ( spl7_72
  <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f3904,plain,
    ( r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1)
    | ~ spl7_1
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f76,f3398,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3901,plain,
    ( spl7_71
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f2555,f2531,f79,f74,f3898])).

fof(f3898,plain,
    ( spl7_71
  <=> r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f2531,plain,
    ( spl7_54
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f2555,plain,
    ( r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)),k2_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_54 ),
    inference(unit_resulting_resolution,[],[f76,f81,f2533,f70])).

fof(f2533,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(sK2))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f2531])).

fof(f3896,plain,
    ( spl7_70
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f1541,f1466,f3893])).

fof(f1466,plain,
    ( spl7_41
  <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f1541,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k2_relat_1(sK6(sK1,sK0)))
    | ~ spl7_41 ),
    inference(unit_resulting_resolution,[],[f1468,f285])).

fof(f1468,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),sK1))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f3891,plain,
    ( spl7_69
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f1486,f1461,f3888])).

fof(f3888,plain,
    ( spl7_69
  <=> r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK6(sK1,sK0))),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f1461,plain,
    ( spl7_40
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f1486,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK6(sK1,sK0))),sK0),sK1)
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f1463,f285])).

fof(f1463,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(sK1,sK0))))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f1461])).

fof(f3399,plain,
    ( spl7_68
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f202,f84,f3396])).

fof(f202,plain,
    ( r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f86,f154])).

fof(f3022,plain,
    ( spl7_67
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f143,f84,f3019])).

fof(f143,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f86,f134])).

fof(f3017,plain,
    ( spl7_66
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f1297,f817,f3014])).

fof(f3014,plain,
    ( spl7_66
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f817,plain,
    ( spl7_38
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f1297,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f819,f285])).

fof(f819,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),sK1))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f817])).

fof(f3012,plain,
    ( spl7_65
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f1248,f812,f3009])).

fof(f3009,plain,
    ( spl7_65
  <=> r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(sK2))),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f812,plain,
    ( spl7_37
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f1248,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(sK2))),sK0),sK1)
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f814,f285])).

fof(f814,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(sK2))))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f812])).

fof(f2980,plain,
    ( spl7_64
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f1113,f347,f116,f2977])).

fof(f2977,plain,
    ( spl7_64
  <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k2_relat_1(sK2),sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f347,plain,
    ( spl7_23
  <=> r2_hidden(sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1113,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k2_relat_1(sK2),sK0)),sK1))
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f118,f862,f184])).

fof(f862,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK2),X0)))
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f845,f402])).

fof(f402,plain,
    ( ! [X0] : k1_funct_1(sK6(k2_relat_1(sK2),X0),sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0))) = X0
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f349,f62])).

fof(f349,plain,
    ( r2_hidden(sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f347])).

fof(f845,plain,
    ( ! [X0] : r2_hidden(k1_funct_1(sK6(k2_relat_1(sK2),X0),sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0))),k2_relat_1(sK6(k2_relat_1(sK2),X0)))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f349,f136])).

fof(f2975,plain,
    ( spl7_63
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f1081,f347,f116,f2972])).

fof(f2972,plain,
    ( spl7_63
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k2_relat_1(sK2),sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f1081,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k2_relat_1(sK2),sK0))))
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f118,f862,f184])).

fof(f2819,plain,
    ( spl7_62
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f965,f270,f122,f74,f2816])).

fof(f2816,plain,
    ( spl7_62
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f270,plain,
    ( spl7_17
  <=> r2_hidden(sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f965,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(sK1,sK0)))))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f911,f97])).

fof(f911,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),k2_relat_1(sK6(sK1,sK0))))
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f124,f858,f184])).

fof(f858,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(sK6(sK1,X0)))
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f849,f295])).

fof(f295,plain,
    ( ! [X0] : k1_funct_1(sK6(sK1,X0),sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0))) = X0
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f272,f62])).

fof(f272,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f270])).

fof(f849,plain,
    ( ! [X0] : r2_hidden(k1_funct_1(sK6(sK1,X0),sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0))),k2_relat_1(sK6(sK1,X0)))
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f272,f136])).

fof(f2814,plain,
    ( spl7_61
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f941,f270,f122,f2811])).

fof(f2811,plain,
    ( spl7_61
  <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f941,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),k1_relat_1(sK2)))
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f124,f858,f184])).

fof(f2809,plain,
    ( spl7_60
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f643,f579,f2806])).

fof(f2806,plain,
    ( spl7_60
  <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f579,plain,
    ( spl7_30
  <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f643,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k3_xboole_0(sK1,sK1))
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f581,f581,f184])).

fof(f581,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),sK1)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f579])).

fof(f2804,plain,
    ( spl7_59
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f631,f574,f116,f2801])).

fof(f2801,plain,
    ( spl7_59
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK1),sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f574,plain,
    ( spl7_29
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f631,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK1),sK1),sK1))
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f118,f576,f184])).

fof(f576,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f574])).

fof(f2799,plain,
    ( spl7_58
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f751,f122,f2796])).

fof(f2796,plain,
    ( spl7_58
  <=> sK0 = k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK5(k6_relat_1(k1_relat_1(sK2)),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f751,plain,
    ( sK0 = k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK5(k6_relat_1(k1_relat_1(sK2)),sK0))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f124,f251])).

fof(f2794,plain,
    ( spl7_57
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f620,f574,f116,f2791])).

fof(f2791,plain,
    ( spl7_57
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f620,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)))
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f118,f576,f184])).

fof(f2789,plain,
    ( spl7_56
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f602,f569,f116,f2786])).

fof(f2786,plain,
    ( spl7_56
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f569,plain,
    ( spl7_28
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f602,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)),sK1))
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f118,f571,f184])).

fof(f571,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f569])).

fof(f2784,plain,
    ( spl7_55
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f592,f569,f116,f2781])).

fof(f2781,plain,
    ( spl7_55
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f592,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))))
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f118,f571,f184])).

fof(f2534,plain,
    ( spl7_54
    | ~ spl7_1
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f2503,f2077,f74,f2531])).

fof(f2077,plain,
    ( spl7_50
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f2503,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_50 ),
    inference(unit_resulting_resolution,[],[f76,f2079,f64])).

fof(f2079,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f2220,plain,
    ( spl7_53
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f1027,f229,f116,f2217])).

fof(f2217,plain,
    ( spl7_53
  <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f1027,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),sK1))
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f118,f863,f184])).

fof(f2215,plain,
    ( spl7_52
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f996,f229,f116,f2212])).

fof(f2212,plain,
    ( spl7_52
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k1_relat_1(sK2),sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f996,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k1_relat_1(sK2),sK0))))
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f118,f863,f184])).

fof(f2085,plain,
    ( spl7_51
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f703,f656,f2082])).

fof(f2082,plain,
    ( spl7_51
  <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f703,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1)
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f658,f285])).

fof(f2080,plain,
    ( spl7_50
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f670,f651,f2077])).

fof(f670,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f653,f285])).

fof(f2075,plain,
    ( spl7_49
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f564,f538,f122,f74,f2072])).

fof(f2072,plain,
    ( spl7_49
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f564,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,k1_relat_1(sK2)))))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f76,f124,f540,f65])).

fof(f2070,plain,
    ( spl7_48
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f558,f538,f122,f2067])).

fof(f2067,plain,
    ( spl7_48
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f558,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k1_relat_1(sK2)))
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f124,f540,f184])).

fof(f2049,plain,
    ( spl7_47
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f529,f507,f2046])).

fof(f2046,plain,
    ( spl7_47
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f529,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK1)))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f509,f509,f184])).

fof(f1823,plain,
    ( spl7_46
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f480,f138,f1820])).

fof(f1820,plain,
    ( spl7_46
  <=> r2_hidden(k1_funct_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f138,plain,
    ( spl7_7
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f480,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f140,f140,f184])).

fof(f140,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1818,plain,
    ( spl7_45
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f474,f188,f116,f1815])).

fof(f474,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))))
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f190,f118,f184])).

fof(f1813,plain,
    ( spl7_44
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f444,f188,f116,f1810])).

fof(f1810,plain,
    ( spl7_44
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f444,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),sK1))
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f118,f190,f184])).

fof(f1808,plain,
    ( spl7_43
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f435,f122,f84,f1805])).

fof(f1805,plain,
    ( spl7_43
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f435,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)))
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f124,f86,f184])).

fof(f1611,plain,
    ( spl7_42
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f753,f116,f1608])).

fof(f1608,plain,
    ( spl7_42
  <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f753,plain,
    ( sK0 = k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f118,f251])).

fof(f1469,plain,
    ( spl7_41
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f943,f270,f116,f1466])).

fof(f943,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),sK1))
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f118,f858,f184])).

fof(f1464,plain,
    ( spl7_40
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f913,f270,f116,f1461])).

fof(f913,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(sK1,sK0))))
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f118,f858,f184])).

fof(f1451,plain,
    ( spl7_39
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f583,f569,f1448])).

fof(f1448,plain,
    ( spl7_39
  <=> r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f583,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1)
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f571,f285])).

fof(f820,plain,
    ( spl7_38
    | ~ spl7_5
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f560,f538,f116,f817])).

fof(f560,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),sK1))
    | ~ spl7_5
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f118,f540,f184])).

fof(f815,plain,
    ( spl7_37
    | ~ spl7_5
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f551,f538,f116,f812])).

fof(f551,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(sK2))))
    | ~ spl7_5
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f118,f540,f184])).

fof(f810,plain,
    ( spl7_36
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f531,f507,f122,f74,f807])).

fof(f807,plain,
    ( spl7_36
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f531,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,sK1))))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f76,f124,f509,f65])).

fof(f805,plain,
    ( spl7_35
    | ~ spl7_6
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f526,f507,f122,f802])).

fof(f802,plain,
    ( spl7_35
  <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f526,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(sK2)))
    | ~ spl7_6
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f124,f509,f184])).

fof(f669,plain,
    ( spl7_34
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f490,f211,f666])).

fof(f490,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f213,f213,f184])).

fof(f664,plain,
    ( spl7_33
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f481,f158,f661])).

fof(f661,plain,
    ( spl7_33
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f158,plain,
    ( spl7_8
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f481,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f160,f160,f184])).

fof(f160,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f659,plain,
    ( spl7_32
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f473,f116,f84,f656])).

fof(f473,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f86,f118,f184])).

fof(f654,plain,
    ( spl7_31
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f437,f116,f84,f651])).

fof(f437,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1))
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f118,f86,f184])).

fof(f582,plain,
    ( spl7_30
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f542,f538,f579])).

fof(f542,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),sK1)
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f540,f285])).

fof(f577,plain,
    ( spl7_29
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f528,f507,f116,f574])).

fof(f528,plain,
    ( r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f118,f509,f184])).

fof(f572,plain,
    ( spl7_28
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f520,f507,f116,f569])).

fof(f520,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f118,f509,f184])).

fof(f541,plain,
    ( spl7_27
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f477,f122,f116,f538])).

fof(f477,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f124,f118,f184])).

fof(f510,plain,
    ( spl7_26
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f479,f116,f507])).

fof(f479,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f118,f118,f184])).

fof(f430,plain,
    ( spl7_25
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f376,f122,f79,f74,f427])).

fof(f427,plain,
    ( spl7_25
  <=> k1_funct_1(k5_relat_1(sK2,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f376,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK2,sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f76,f81,f76,f81,f124,f58])).

fof(f355,plain,
    ( spl7_24
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f234,f229,f79,f74,f352])).

fof(f352,plain,
    ( spl7_24
  <=> r2_hidden(k1_funct_1(sK2,sK5(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f234,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f76,f81,f231,f70])).

fof(f350,plain,
    ( spl7_23
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f206,f138,f347])).

fof(f206,plain,
    ( r2_hidden(sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f140,f154])).

fof(f345,plain,
    ( spl7_22
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f194,f188,f122,f74,f342])).

fof(f342,plain,
    ( spl7_22
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f194,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f76,f124,f190,f65])).

fof(f340,plain,
    ( spl7_21
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f169,f165,f79,f74,f337])).

fof(f337,plain,
    ( spl7_21
  <=> r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f165,plain,
    ( spl7_9
  <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f169,plain,
    ( r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f76,f81,f167,f70])).

fof(f167,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f329,plain,
    ( spl7_20
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f313,f138,f122,f79,f74,f326])).

fof(f313,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f76,f81,f124,f140,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f312,plain,
    ( spl7_19
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f146,f138,f309])).

fof(f309,plain,
    ( spl7_19
  <=> r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f146,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f140,f134])).

fof(f278,plain,
    ( spl7_18
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f226,f211,f275])).

fof(f275,plain,
    ( spl7_18
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f226,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f213,f134])).

fof(f273,plain,
    ( spl7_17
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f225,f211,f270])).

fof(f225,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f213,f154])).

fof(f268,plain,
    ( spl7_16
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f207,f158,f265])).

fof(f265,plain,
    ( spl7_16
  <=> r2_hidden(sK5(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f207,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f160,f154])).

fof(f263,plain,
    ( spl7_15
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f162,f158,f260])).

fof(f260,plain,
    ( spl7_15
  <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f162,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f160,f134])).

fof(f243,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f177,f122,f84,f74,f240])).

fof(f240,plain,
    ( spl7_14
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f177,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK1)))))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f76,f86,f124,f65])).

fof(f232,plain,
    ( spl7_13
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f204,f122,f229])).

fof(f204,plain,
    ( r2_hidden(sK5(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f124,f154])).

fof(f214,plain,
    ( spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f205,f116,f211])).

fof(f205,plain,
    ( r2_hidden(sK5(k6_relat_1(sK1),sK0),sK1)
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f118,f154])).

fof(f191,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f178,f122,f74,f188])).

fof(f178,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f76,f124,f124,f65])).

fof(f176,plain,
    ( spl7_10
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f147,f138,f79,f74,f173])).

fof(f173,plain,
    ( spl7_10
  <=> r2_hidden(sK5(sK2,k1_funct_1(sK2,sK0)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f147,plain,
    ( r2_hidden(sK5(sK2,k1_funct_1(sK2,sK0)),k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f76,f81,f140,f72])).

fof(f168,plain,
    ( spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f144,f122,f165])).

fof(f144,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f124,f134])).

fof(f161,plain,
    ( spl7_8
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f145,f116,f158])).

fof(f145,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),sK1)
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f118,f134])).

fof(f141,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f127,f122,f79,f74,f138])).

fof(f127,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f76,f81,f124,f70])).

fof(f125,plain,
    ( spl7_6
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f107,f84,f74,f122])).

fof(f107,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f76,f86,f64])).

fof(f119,plain,
    ( spl7_5
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f106,f84,f74,f116])).

fof(f106,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f76,f86,f63])).

fof(f92,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f87,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f43,f84])).

fof(f43,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f42,f79])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:54:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (20253)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.45  % (20245)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.46  % (20251)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (20244)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (20240)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (20243)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.51  % (20240)Refutation not found, incomplete strategy% (20240)------------------------------
% 0.19/0.51  % (20240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (20240)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (20240)Memory used [KB]: 10618
% 0.19/0.51  % (20240)Time elapsed: 0.090 s
% 0.19/0.51  % (20240)------------------------------
% 0.19/0.51  % (20240)------------------------------
% 0.19/0.52  % (20252)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.52  % (20259)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.52  % (20255)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.52  % (20259)Refutation not found, incomplete strategy% (20259)------------------------------
% 0.19/0.52  % (20259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (20259)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  % (20250)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.52  
% 0.19/0.52  % (20259)Memory used [KB]: 10618
% 0.19/0.52  % (20259)Time elapsed: 0.120 s
% 0.19/0.52  % (20259)------------------------------
% 0.19/0.52  % (20259)------------------------------
% 0.19/0.53  % (20254)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.53  % (20241)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.53  % (20239)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.54  % (20248)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.54  % (20242)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.54  % (20256)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.54  % (20246)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.55  % (20258)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.55  % (20247)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.56  % (20249)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.56  % (20257)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 4.34/0.90  % (20251)Time limit reached!
% 4.34/0.90  % (20251)------------------------------
% 4.34/0.90  % (20251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.90  % (20251)Termination reason: Time limit
% 4.34/0.90  % (20251)Termination phase: Saturation
% 4.34/0.90  
% 4.34/0.90  % (20251)Memory used [KB]: 12281
% 4.34/0.90  % (20251)Time elapsed: 0.500 s
% 4.34/0.90  % (20251)------------------------------
% 4.34/0.90  % (20251)------------------------------
% 4.34/0.92  % (20244)Time limit reached!
% 4.34/0.92  % (20244)------------------------------
% 4.34/0.92  % (20244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.92  % (20244)Termination reason: Time limit
% 4.34/0.92  % (20244)Termination phase: Saturation
% 4.34/0.92  
% 4.34/0.92  % (20244)Memory used [KB]: 10106
% 4.34/0.92  % (20244)Time elapsed: 0.500 s
% 4.34/0.92  % (20244)------------------------------
% 4.34/0.92  % (20244)------------------------------
% 4.34/0.92  % (20239)Time limit reached!
% 4.34/0.92  % (20239)------------------------------
% 4.34/0.92  % (20239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.92  % (20239)Termination reason: Time limit
% 4.34/0.92  
% 4.34/0.92  % (20239)Memory used [KB]: 12153
% 4.34/0.92  % (20239)Time elapsed: 0.516 s
% 4.34/0.92  % (20239)------------------------------
% 4.34/0.92  % (20239)------------------------------
% 4.63/0.93  % (20249)Time limit reached!
% 4.63/0.93  % (20249)------------------------------
% 4.63/0.93  % (20249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/0.93  % (20249)Termination reason: Time limit
% 4.63/0.93  
% 4.63/0.93  % (20249)Memory used [KB]: 11385
% 4.63/0.93  % (20249)Time elapsed: 0.528 s
% 4.63/0.93  % (20249)------------------------------
% 4.63/0.93  % (20249)------------------------------
% 4.63/1.00  % (20246)Refutation found. Thanks to Tanya!
% 4.63/1.00  % SZS status Theorem for theBenchmark
% 4.63/1.00  % SZS output start Proof for theBenchmark
% 4.63/1.00  fof(f6687,plain,(
% 4.63/1.00    $false),
% 4.63/1.00    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f119,f125,f141,f161,f168,f176,f191,f214,f232,f243,f263,f268,f273,f278,f312,f329,f340,f345,f350,f355,f430,f510,f541,f572,f577,f582,f654,f659,f664,f669,f805,f810,f815,f820,f1451,f1464,f1469,f1611,f1808,f1813,f1818,f1823,f2049,f2070,f2075,f2080,f2085,f2215,f2220,f2534,f2784,f2789,f2794,f2799,f2804,f2809,f2814,f2819,f2975,f2980,f3012,f3017,f3022,f3399,f3891,f3896,f3901,f3933,f4249,f4257,f4428,f4433,f4677,f4682,f5317,f5322,f5327,f5332,f5337,f5344,f5351,f5356,f5361,f5366,f5371,f5376,f5381,f5386,f5391,f5663,f6479,f6616,f6686])).
% 4.63/1.00  fof(f6686,plain,(
% 4.63/1.00    ~spl7_1 | ~spl7_2 | spl7_4 | ~spl7_5 | ~spl7_73),
% 4.63/1.00    inference(avatar_contradiction_clause,[],[f6685])).
% 4.63/1.00  fof(f6685,plain,(
% 4.63/1.00    $false | (~spl7_1 | ~spl7_2 | spl7_4 | ~spl7_5 | ~spl7_73)),
% 4.63/1.00    inference(subsumption_resolution,[],[f6684,f118])).
% 4.63/1.00  fof(f118,plain,(
% 4.63/1.00    r2_hidden(sK0,sK1) | ~spl7_5),
% 4.63/1.00    inference(avatar_component_clause,[],[f116])).
% 4.63/1.00  fof(f116,plain,(
% 4.63/1.00    spl7_5 <=> r2_hidden(sK0,sK1)),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 4.63/1.00  fof(f6684,plain,(
% 4.63/1.00    ~r2_hidden(sK0,sK1) | (~spl7_1 | ~spl7_2 | spl7_4 | ~spl7_73)),
% 4.63/1.00    inference(subsumption_resolution,[],[f6603,f91])).
% 4.63/1.00  fof(f91,plain,(
% 4.63/1.00    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) | spl7_4),
% 4.63/1.00    inference(avatar_component_clause,[],[f89])).
% 4.63/1.00  fof(f89,plain,(
% 4.63/1.00    spl7_4 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 4.63/1.00  fof(f6603,plain,(
% 4.63/1.00    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | ~r2_hidden(sK0,sK1) | (~spl7_1 | ~spl7_2 | ~spl7_73)),
% 4.63/1.00    inference(superposition,[],[f1801,f4248])).
% 4.63/1.00  fof(f4248,plain,(
% 4.63/1.00    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) | ~spl7_73),
% 4.63/1.00    inference(avatar_component_clause,[],[f4246])).
% 4.63/1.00  fof(f4246,plain,(
% 4.63/1.00    spl7_73 <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 4.63/1.00  fof(f1801,plain,(
% 4.63/1.00    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,X1)) ) | (~spl7_1 | ~spl7_2)),
% 4.63/1.00    inference(forward_demodulation,[],[f1800,f47])).
% 4.63/1.00  fof(f47,plain,(
% 4.63/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.63/1.00    inference(cnf_transformation,[],[f1])).
% 4.63/1.00  fof(f1,axiom,(
% 4.63/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 4.63/1.00  fof(f1800,plain,(
% 4.63/1.00    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))) ) | (~spl7_1 | ~spl7_2)),
% 4.63/1.00    inference(forward_demodulation,[],[f1799,f93])).
% 4.63/1.00  fof(f93,plain,(
% 4.63/1.00    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl7_1),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f76,f55])).
% 4.63/1.00  fof(f55,plain,(
% 4.63/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 4.63/1.00    inference(cnf_transformation,[],[f17])).
% 4.63/1.00  fof(f17,plain,(
% 4.63/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 4.63/1.00    inference(ennf_transformation,[],[f4])).
% 4.63/1.00  fof(f4,axiom,(
% 4.63/1.00    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 4.63/1.00  fof(f76,plain,(
% 4.63/1.00    v1_relat_1(sK2) | ~spl7_1),
% 4.63/1.00    inference(avatar_component_clause,[],[f74])).
% 4.63/1.00  fof(f74,plain,(
% 4.63/1.00    spl7_1 <=> v1_relat_1(sK2)),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 4.63/1.00  fof(f1799,plain,(
% 4.63/1.00    ( ! [X2,X1] : (k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))) ) | (~spl7_1 | ~spl7_2)),
% 4.63/1.00    inference(subsumption_resolution,[],[f1795,f45])).
% 4.63/1.00  fof(f45,plain,(
% 4.63/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.63/1.00    inference(cnf_transformation,[],[f6])).
% 4.63/1.00  fof(f6,axiom,(
% 4.63/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 4.63/1.00  fof(f1795,plain,(
% 4.63/1.00    ( ! [X2,X1] : (k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl7_1 | ~spl7_2)),
% 4.63/1.00    inference(resolution,[],[f394,f46])).
% 4.63/1.00  fof(f46,plain,(
% 4.63/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 4.63/1.00    inference(cnf_transformation,[],[f6])).
% 4.63/1.00  fof(f394,plain,(
% 4.63/1.00    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | (~spl7_1 | ~spl7_2)),
% 4.63/1.00    inference(subsumption_resolution,[],[f388,f76])).
% 4.63/1.00  fof(f388,plain,(
% 4.63/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0)) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl7_2),
% 4.63/1.00    inference(resolution,[],[f58,f81])).
% 4.63/1.00  fof(f81,plain,(
% 4.63/1.00    v1_funct_1(sK2) | ~spl7_2),
% 4.63/1.00    inference(avatar_component_clause,[],[f79])).
% 4.63/1.00  fof(f79,plain,(
% 4.63/1.00    spl7_2 <=> v1_funct_1(sK2)),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 4.63/1.00  fof(f58,plain,(
% 4.63/1.00    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.63/1.00    inference(cnf_transformation,[],[f22])).
% 4.63/1.00  fof(f22,plain,(
% 4.63/1.00    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.63/1.00    inference(flattening,[],[f21])).
% 4.63/1.00  fof(f21,plain,(
% 4.63/1.00    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.63/1.00    inference(ennf_transformation,[],[f9])).
% 4.63/1.00  fof(f9,axiom,(
% 4.63/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 4.63/1.00  fof(f6616,plain,(
% 4.63/1.00    ~spl7_1 | ~spl7_2 | spl7_4 | ~spl7_5 | ~spl7_73),
% 4.63/1.00    inference(avatar_contradiction_clause,[],[f6615])).
% 4.63/1.00  fof(f6615,plain,(
% 4.63/1.00    $false | (~spl7_1 | ~spl7_2 | spl7_4 | ~spl7_5 | ~spl7_73)),
% 4.63/1.00    inference(subsumption_resolution,[],[f6614,f91])).
% 4.63/1.00  fof(f6614,plain,(
% 4.63/1.00    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | (~spl7_1 | ~spl7_2 | ~spl7_5 | ~spl7_73)),
% 4.63/1.00    inference(forward_demodulation,[],[f6554,f4248])).
% 4.63/1.00  fof(f6554,plain,(
% 4.63/1.00    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | (~spl7_1 | ~spl7_2 | ~spl7_5)),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f118,f1801])).
% 4.63/1.00  fof(f6479,plain,(
% 4.63/1.00    spl7_95 | ~spl7_81),
% 4.63/1.00    inference(avatar_split_clause,[],[f6424,f5324,f6476])).
% 4.63/1.00  fof(f6476,plain,(
% 4.63/1.00    spl7_95 <=> r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1)),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).
% 4.63/1.00  fof(f5324,plain,(
% 4.63/1.00    spl7_81 <=> r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1))),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 4.63/1.00  fof(f6424,plain,(
% 4.63/1.00    r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1) | ~spl7_81),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f5326,f112])).
% 4.63/1.00  fof(f112,plain,(
% 4.63/1.00    ( ! [X4,X2,X3] : (r2_hidden(X2,X3) | ~r2_hidden(X2,k3_xboole_0(X3,X4))) )),
% 4.63/1.00    inference(forward_demodulation,[],[f111,f47])).
% 4.63/1.00  fof(f111,plain,(
% 4.63/1.00    ( ! [X4,X2,X3] : (~r2_hidden(X2,k3_xboole_0(X3,X4)) | r2_hidden(X2,k1_relat_1(k6_relat_1(X3)))) )),
% 4.63/1.00    inference(forward_demodulation,[],[f109,f103])).
% 4.63/1.00  fof(f103,plain,(
% 4.63/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X0,X1)) )),
% 4.63/1.00    inference(forward_demodulation,[],[f98,f47])).
% 4.63/1.00  fof(f98,plain,(
% 4.63/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f45,f56])).
% 4.63/1.00  fof(f56,plain,(
% 4.63/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.63/1.00    inference(cnf_transformation,[],[f18])).
% 4.63/1.00  fof(f18,plain,(
% 4.63/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.63/1.00    inference(ennf_transformation,[],[f3])).
% 4.63/1.00  fof(f3,axiom,(
% 4.63/1.00    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 4.63/1.00  fof(f109,plain,(
% 4.63/1.00    ( ! [X4,X2,X3] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) | r2_hidden(X2,k1_relat_1(k6_relat_1(X3)))) )),
% 4.63/1.00    inference(resolution,[],[f64,f45])).
% 4.63/1.00  fof(f64,plain,(
% 4.63/1.00    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2))) )),
% 4.63/1.00    inference(cnf_transformation,[],[f38])).
% 4.63/1.00  fof(f38,plain,(
% 4.63/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 4.63/1.00    inference(flattening,[],[f37])).
% 4.63/1.00  fof(f37,plain,(
% 4.63/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 4.63/1.00    inference(nnf_transformation,[],[f24])).
% 4.63/1.00  fof(f24,plain,(
% 4.63/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 4.63/1.00    inference(ennf_transformation,[],[f2])).
% 4.63/1.00  fof(f2,axiom,(
% 4.63/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 4.63/1.00  fof(f5326,plain,(
% 4.63/1.00    r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1)) | ~spl7_81),
% 4.63/1.00    inference(avatar_component_clause,[],[f5324])).
% 4.63/1.00  fof(f5663,plain,(
% 4.63/1.00    spl7_94 | ~spl7_45),
% 4.63/1.00    inference(avatar_split_clause,[],[f1954,f1815,f5660])).
% 4.63/1.00  fof(f5660,plain,(
% 4.63/1.00    spl7_94 <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),sK0),sK1)),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).
% 4.63/1.00  fof(f1815,plain,(
% 4.63/1.00    spl7_45 <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))))),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 4.63/1.00  fof(f1954,plain,(
% 4.63/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),sK0),sK1) | ~spl7_45),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f1817,f285])).
% 4.63/1.00  fof(f285,plain,(
% 4.63/1.00    ( ! [X4,X2,X3] : (r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4) | ~r2_hidden(X2,k3_xboole_0(X4,X3))) )),
% 4.63/1.00    inference(forward_demodulation,[],[f284,f103])).
% 4.63/1.00  fof(f284,plain,(
% 4.63/1.00    ( ! [X4,X2,X3] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X4),X3))) | r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4)) )),
% 4.63/1.00    inference(forward_demodulation,[],[f283,f94])).
% 4.63/1.00  fof(f94,plain,(
% 4.63/1.00    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f45,f55])).
% 4.63/1.00  fof(f283,plain,(
% 4.63/1.00    ( ! [X4,X2,X3] : (~r2_hidden(X2,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)))) | r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4)) )),
% 4.63/1.00    inference(subsumption_resolution,[],[f280,f45])).
% 4.63/1.00  fof(f280,plain,(
% 4.63/1.00    ( ! [X4,X2,X3] : (~r2_hidden(X2,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)))) | r2_hidden(k1_funct_1(k6_relat_1(X3),X2),X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 4.63/1.00    inference(resolution,[],[f67,f46])).
% 4.63/1.00  fof(f67,plain,(
% 4.63/1.00    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | r2_hidden(k1_funct_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 4.63/1.00    inference(cnf_transformation,[],[f40])).
% 4.63/1.00  fof(f40,plain,(
% 4.63/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.63/1.00    inference(flattening,[],[f39])).
% 4.63/1.00  fof(f39,plain,(
% 4.63/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.63/1.00    inference(nnf_transformation,[],[f26])).
% 4.63/1.00  fof(f26,plain,(
% 4.63/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.63/1.00    inference(flattening,[],[f25])).
% 4.63/1.00  fof(f25,plain,(
% 4.63/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.63/1.00    inference(ennf_transformation,[],[f10])).
% 4.63/1.00  fof(f10,axiom,(
% 4.63/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).
% 4.63/1.00  fof(f1817,plain,(
% 4.63/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))) | ~spl7_45),
% 4.63/1.00    inference(avatar_component_clause,[],[f1815])).
% 4.63/1.00  fof(f5391,plain,(
% 4.63/1.00    spl7_93 | ~spl7_3),
% 4.63/1.00    inference(avatar_split_clause,[],[f747,f84,f5388])).
% 4.63/1.00  fof(f5388,plain,(
% 4.63/1.00    spl7_93 <=> sK0 = k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0))),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).
% 4.63/1.00  fof(f84,plain,(
% 4.63/1.00    spl7_3 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 4.63/1.00  fof(f747,plain,(
% 4.63/1.00    sK0 = k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0)) | ~spl7_3),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f86,f251])).
% 4.63/1.00  fof(f251,plain,(
% 4.63/1.00    ( ! [X2,X1] : (k1_funct_1(k6_relat_1(X2),sK5(k6_relat_1(X2),X1)) = X1 | ~r2_hidden(X1,X2)) )),
% 4.63/1.00    inference(forward_demodulation,[],[f250,f48])).
% 4.63/1.00  fof(f48,plain,(
% 4.63/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.63/1.00    inference(cnf_transformation,[],[f1])).
% 4.63/1.00  fof(f250,plain,(
% 4.63/1.00    ( ! [X2,X1] : (~r2_hidden(X1,k2_relat_1(k6_relat_1(X2))) | k1_funct_1(k6_relat_1(X2),sK5(k6_relat_1(X2),X1)) = X1) )),
% 4.63/1.00    inference(subsumption_resolution,[],[f246,f45])).
% 4.63/1.00  fof(f246,plain,(
% 4.63/1.00    ( ! [X2,X1] : (~r2_hidden(X1,k2_relat_1(k6_relat_1(X2))) | k1_funct_1(k6_relat_1(X2),sK5(k6_relat_1(X2),X1)) = X1 | ~v1_relat_1(k6_relat_1(X2))) )),
% 4.63/1.00    inference(resolution,[],[f71,f46])).
% 4.63/1.00  fof(f71,plain,(
% 4.63/1.00    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK5(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 4.63/1.00    inference(equality_resolution,[],[f50])).
% 4.63/1.00  fof(f50,plain,(
% 4.63/1.00    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.63/1.00    inference(cnf_transformation,[],[f34])).
% 4.63/1.00  fof(f34,plain,(
% 4.63/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 4.63/1.00  fof(f31,plain,(
% 4.63/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 4.63/1.00    introduced(choice_axiom,[])).
% 4.63/1.00  fof(f32,plain,(
% 4.63/1.00    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 4.63/1.00    introduced(choice_axiom,[])).
% 4.63/1.00  fof(f33,plain,(
% 4.63/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 4.63/1.00    introduced(choice_axiom,[])).
% 4.63/1.00  fof(f30,plain,(
% 4.63/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.63/1.00    inference(rectify,[],[f29])).
% 4.63/1.00  fof(f29,plain,(
% 4.63/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.63/1.00    inference(nnf_transformation,[],[f16])).
% 4.63/1.00  fof(f16,plain,(
% 4.63/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.63/1.00    inference(flattening,[],[f15])).
% 4.63/1.00  fof(f15,plain,(
% 4.63/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.63/1.00    inference(ennf_transformation,[],[f5])).
% 4.63/1.00  fof(f5,axiom,(
% 4.63/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 4.63/1.00  fof(f86,plain,(
% 4.63/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl7_3),
% 4.63/1.00    inference(avatar_component_clause,[],[f84])).
% 4.63/1.00  fof(f5386,plain,(
% 4.63/1.00    spl7_92 | ~spl7_1 | ~spl7_6 | ~spl7_13),
% 4.63/1.00    inference(avatar_split_clause,[],[f1049,f229,f122,f74,f5383])).
% 4.63/1.00  fof(f5383,plain,(
% 4.63/1.00    spl7_92 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(k1_relat_1(sK2),sK0)))))),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 4.63/1.00  fof(f122,plain,(
% 4.63/1.00    spl7_6 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 4.63/1.00  fof(f229,plain,(
% 4.63/1.00    spl7_13 <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2))),
% 4.63/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 4.63/1.00  fof(f1049,plain,(
% 4.63/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(k1_relat_1(sK2),sK0))))) | (~spl7_1 | ~spl7_6 | ~spl7_13)),
% 4.63/1.00    inference(forward_demodulation,[],[f994,f97])).
% 4.63/1.00  fof(f97,plain,(
% 4.63/1.00    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)) ) | ~spl7_1),
% 4.63/1.00    inference(unit_resulting_resolution,[],[f76,f56])).
% 5.24/1.00  fof(f994,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),k2_relat_1(sK6(k1_relat_1(sK2),sK0)))) | (~spl7_6 | ~spl7_13)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f863,f184])).
% 5.24/1.00  fof(f184,plain,(
% 5.24/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) )),
% 5.24/1.00    inference(forward_demodulation,[],[f183,f47])).
% 5.24/1.00  fof(f183,plain,(
% 5.24/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~r2_hidden(X2,X1)) )),
% 5.24/1.00    inference(subsumption_resolution,[],[f181,f45])).
% 5.24/1.00  fof(f181,plain,(
% 5.24/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~r2_hidden(X2,X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 5.24/1.00    inference(superposition,[],[f65,f103])).
% 5.24/1.00  fof(f65,plain,(
% 5.24/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 5.24/1.00    inference(cnf_transformation,[],[f38])).
% 5.24/1.00  fof(f863,plain,(
% 5.24/1.00    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(k1_relat_1(sK2),X0)))) ) | ~spl7_13),
% 5.24/1.00    inference(forward_demodulation,[],[f844,f238])).
% 5.24/1.00  fof(f238,plain,(
% 5.24/1.00    ( ! [X0] : (k1_funct_1(sK6(k1_relat_1(sK2),X0),sK5(k6_relat_1(k1_relat_1(sK2)),sK0)) = X0) ) | ~spl7_13),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f231,f62])).
% 5.24/1.00  fof(f62,plain,(
% 5.24/1.00    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 5.24/1.00    inference(cnf_transformation,[],[f36])).
% 5.24/1.00  fof(f36,plain,(
% 5.24/1.00    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 5.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f35])).
% 5.24/1.00  fof(f35,plain,(
% 5.24/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 5.24/1.00    introduced(choice_axiom,[])).
% 5.24/1.00  fof(f23,plain,(
% 5.24/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 5.24/1.00    inference(ennf_transformation,[],[f7])).
% 5.24/1.00  fof(f7,axiom,(
% 5.24/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 5.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 5.24/1.00  fof(f231,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2)) | ~spl7_13),
% 5.24/1.00    inference(avatar_component_clause,[],[f229])).
% 5.24/1.00  fof(f844,plain,(
% 5.24/1.00    ( ! [X0] : (r2_hidden(k1_funct_1(sK6(k1_relat_1(sK2),X0),sK5(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK6(k1_relat_1(sK2),X0)))) ) | ~spl7_13),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f231,f136])).
% 5.24/1.00  fof(f136,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (r2_hidden(k1_funct_1(sK6(X4,X5),X3),k2_relat_1(sK6(X4,X5))) | ~r2_hidden(X3,X4)) )),
% 5.24/1.00    inference(forward_demodulation,[],[f135,f61])).
% 5.24/1.00  fof(f61,plain,(
% 5.24/1.00    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 5.24/1.00    inference(cnf_transformation,[],[f36])).
% 5.24/1.00  fof(f135,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X3,k1_relat_1(sK6(X4,X5))) | r2_hidden(k1_funct_1(sK6(X4,X5),X3),k2_relat_1(sK6(X4,X5)))) )),
% 5.24/1.00    inference(subsumption_resolution,[],[f130,f59])).
% 5.24/1.00  fof(f59,plain,(
% 5.24/1.00    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 5.24/1.00    inference(cnf_transformation,[],[f36])).
% 5.24/1.00  fof(f130,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X3,k1_relat_1(sK6(X4,X5))) | r2_hidden(k1_funct_1(sK6(X4,X5),X3),k2_relat_1(sK6(X4,X5))) | ~v1_relat_1(sK6(X4,X5))) )),
% 5.24/1.00    inference(resolution,[],[f70,f60])).
% 5.24/1.00  fof(f60,plain,(
% 5.24/1.00    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 5.24/1.00    inference(cnf_transformation,[],[f36])).
% 5.24/1.00  fof(f70,plain,(
% 5.24/1.00    ( ! [X6,X0] : (~v1_funct_1(X0) | ~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.24/1.00    inference(equality_resolution,[],[f69])).
% 5.24/1.00  fof(f69,plain,(
% 5.24/1.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.24/1.00    inference(equality_resolution,[],[f51])).
% 5.24/1.00  fof(f51,plain,(
% 5.24/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.24/1.00    inference(cnf_transformation,[],[f34])).
% 5.24/1.00  fof(f124,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_6),
% 5.24/1.00    inference(avatar_component_clause,[],[f122])).
% 5.24/1.00  fof(f5381,plain,(
% 5.24/1.00    spl7_91 | ~spl7_6 | ~spl7_13),
% 5.24/1.00    inference(avatar_split_clause,[],[f1025,f229,f122,f5378])).
% 5.24/1.00  fof(f5378,plain,(
% 5.24/1.00    spl7_91 <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 5.24/1.00  fof(f1025,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),k1_relat_1(sK2))) | (~spl7_6 | ~spl7_13)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f863,f184])).
% 5.24/1.00  fof(f5376,plain,(
% 5.24/1.00    spl7_90 | ~spl7_12 | ~spl7_34),
% 5.24/1.00    inference(avatar_split_clause,[],[f798,f666,f211,f5373])).
% 5.24/1.00  fof(f5373,plain,(
% 5.24/1.00    spl7_90 <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).
% 5.24/1.00  fof(f211,plain,(
% 5.24/1.00    spl7_12 <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 5.24/1.00  fof(f666,plain,(
% 5.24/1.00    spl7_34 <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 5.24/1.00  fof(f798,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) | (~spl7_12 | ~spl7_34)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f213,f668,f184])).
% 5.24/1.00  fof(f668,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1)) | ~spl7_34),
% 5.24/1.00    inference(avatar_component_clause,[],[f666])).
% 5.24/1.00  fof(f213,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK0),sK1) | ~spl7_12),
% 5.24/1.00    inference(avatar_component_clause,[],[f211])).
% 5.24/1.00  fof(f5371,plain,(
% 5.24/1.00    spl7_89 | ~spl7_12 | ~spl7_34),
% 5.24/1.00    inference(avatar_split_clause,[],[f796,f666,f211,f5368])).
% 5.24/1.00  fof(f5368,plain,(
% 5.24/1.00    spl7_89 <=> r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 5.24/1.00  fof(f796,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))) | (~spl7_12 | ~spl7_34)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f213,f668,f184])).
% 5.24/1.00  fof(f5366,plain,(
% 5.24/1.00    spl7_88 | ~spl7_5 | ~spl7_32),
% 5.24/1.00    inference(avatar_split_clause,[],[f725,f656,f116,f5363])).
% 5.24/1.00  fof(f5363,plain,(
% 5.24/1.00    spl7_88 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).
% 5.24/1.00  fof(f656,plain,(
% 5.24/1.00    spl7_32 <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 5.24/1.00  fof(f725,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)) | (~spl7_5 | ~spl7_32)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f658,f184])).
% 5.24/1.00  fof(f658,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1)))) | ~spl7_32),
% 5.24/1.00    inference(avatar_component_clause,[],[f656])).
% 5.24/1.00  fof(f5361,plain,(
% 5.24/1.00    spl7_87 | ~spl7_5 | ~spl7_32),
% 5.24/1.00    inference(avatar_split_clause,[],[f712,f656,f116,f5358])).
% 5.24/1.00  fof(f5358,plain,(
% 5.24/1.00    spl7_87 <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1)))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).
% 5.24/1.00  fof(f712,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))))) | (~spl7_5 | ~spl7_32)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f658,f184])).
% 5.24/1.00  fof(f5356,plain,(
% 5.24/1.00    spl7_86 | ~spl7_5 | ~spl7_31),
% 5.24/1.00    inference(avatar_split_clause,[],[f691,f651,f116,f5353])).
% 5.24/1.00  fof(f5353,plain,(
% 5.24/1.00    spl7_86 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).
% 5.24/1.00  fof(f651,plain,(
% 5.24/1.00    spl7_31 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 5.24/1.00  fof(f691,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1),sK1)) | (~spl7_5 | ~spl7_31)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f653,f184])).
% 5.24/1.00  fof(f653,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1)) | ~spl7_31),
% 5.24/1.00    inference(avatar_component_clause,[],[f651])).
% 5.24/1.00  fof(f5351,plain,(
% 5.24/1.00    spl7_85 | ~spl7_5 | ~spl7_31),
% 5.24/1.00    inference(avatar_split_clause,[],[f679,f651,f116,f5348])).
% 5.24/1.00  fof(f5348,plain,(
% 5.24/1.00    spl7_85 <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 5.24/1.00  fof(f679,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1))) | (~spl7_5 | ~spl7_31)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f653,f184])).
% 5.24/1.00  fof(f5344,plain,(
% 5.24/1.00    spl7_84 | ~spl7_26 | ~spl7_27),
% 5.24/1.00    inference(avatar_split_clause,[],[f561,f538,f507,f5341])).
% 5.24/1.00  fof(f5341,plain,(
% 5.24/1.00    spl7_84 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k3_xboole_0(sK1,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 5.24/1.00  fof(f507,plain,(
% 5.24/1.00    spl7_26 <=> r2_hidden(sK0,k3_xboole_0(sK1,sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 5.24/1.00  fof(f538,plain,(
% 5.24/1.00    spl7_27 <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 5.24/1.00  fof(f561,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k3_xboole_0(sK1,sK1))) | (~spl7_26 | ~spl7_27)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f509,f540,f184])).
% 5.24/1.00  fof(f540,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) | ~spl7_27),
% 5.24/1.00    inference(avatar_component_clause,[],[f538])).
% 5.24/1.00  fof(f509,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,sK1)) | ~spl7_26),
% 5.24/1.00    inference(avatar_component_clause,[],[f507])).
% 5.24/1.00  fof(f5337,plain,(
% 5.24/1.00    spl7_83 | ~spl7_26 | ~spl7_27),
% 5.24/1.00    inference(avatar_split_clause,[],[f552,f538,f507,f5334])).
% 5.24/1.00  fof(f5334,plain,(
% 5.24/1.00    spl7_83 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k1_relat_1(sK2))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).
% 5.24/1.00  fof(f552,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k1_relat_1(sK2)))) | (~spl7_26 | ~spl7_27)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f509,f540,f184])).
% 5.24/1.00  fof(f5332,plain,(
% 5.24/1.00    spl7_82 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f532,f507,f5329])).
% 5.24/1.00  fof(f5329,plain,(
% 5.24/1.00    spl7_82 <=> r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 5.24/1.00  fof(f532,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1)) | ~spl7_26),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f509,f134])).
% 5.24/1.00  fof(f134,plain,(
% 5.24/1.00    ( ! [X2,X1] : (r2_hidden(k1_funct_1(k6_relat_1(X2),X1),X2) | ~r2_hidden(X1,X2)) )),
% 5.24/1.00    inference(forward_demodulation,[],[f133,f48])).
% 5.24/1.00  fof(f133,plain,(
% 5.24/1.00    ( ! [X2,X1] : (~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(k6_relat_1(X2),X1),k2_relat_1(k6_relat_1(X2)))) )),
% 5.24/1.00    inference(forward_demodulation,[],[f132,f47])).
% 5.24/1.00  fof(f132,plain,(
% 5.24/1.00    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(k6_relat_1(X2))) | r2_hidden(k1_funct_1(k6_relat_1(X2),X1),k2_relat_1(k6_relat_1(X2)))) )),
% 5.24/1.00    inference(subsumption_resolution,[],[f129,f45])).
% 5.24/1.00  fof(f129,plain,(
% 5.24/1.00    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(k6_relat_1(X2))) | r2_hidden(k1_funct_1(k6_relat_1(X2),X1),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 5.24/1.00    inference(resolution,[],[f70,f46])).
% 5.24/1.00  fof(f5327,plain,(
% 5.24/1.00    spl7_81 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f530,f507,f5324])).
% 5.24/1.00  fof(f530,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),k3_xboole_0(sK1,sK1)) | ~spl7_26),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f509,f154])).
% 5.24/1.00  fof(f154,plain,(
% 5.24/1.00    ( ! [X2,X1] : (r2_hidden(sK5(k6_relat_1(X2),X1),X2) | ~r2_hidden(X1,X2)) )),
% 5.24/1.00    inference(forward_demodulation,[],[f153,f47])).
% 5.24/1.00  fof(f153,plain,(
% 5.24/1.00    ( ! [X2,X1] : (~r2_hidden(X1,X2) | r2_hidden(sK5(k6_relat_1(X2),X1),k1_relat_1(k6_relat_1(X2)))) )),
% 5.24/1.00    inference(forward_demodulation,[],[f152,f48])).
% 5.24/1.00  fof(f152,plain,(
% 5.24/1.00    ( ! [X2,X1] : (~r2_hidden(X1,k2_relat_1(k6_relat_1(X2))) | r2_hidden(sK5(k6_relat_1(X2),X1),k1_relat_1(k6_relat_1(X2)))) )),
% 5.24/1.00    inference(subsumption_resolution,[],[f149,f45])).
% 5.24/1.00  fof(f149,plain,(
% 5.24/1.00    ( ! [X2,X1] : (~r2_hidden(X1,k2_relat_1(k6_relat_1(X2))) | r2_hidden(sK5(k6_relat_1(X2),X1),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 5.24/1.00    inference(resolution,[],[f72,f46])).
% 5.24/1.00  fof(f72,plain,(
% 5.24/1.00    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.24/1.00    inference(equality_resolution,[],[f49])).
% 5.24/1.00  fof(f49,plain,(
% 5.24/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.24/1.00    inference(cnf_transformation,[],[f34])).
% 5.24/1.00  fof(f5322,plain,(
% 5.24/1.00    spl7_80 | ~spl7_3 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f522,f507,f84,f5319])).
% 5.24/1.00  fof(f5319,plain,(
% 5.24/1.00    spl7_80 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(k7_relat_1(sK2,sK1))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).
% 5.24/1.00  fof(f522,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(k7_relat_1(sK2,sK1)))) | (~spl7_3 | ~spl7_26)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f86,f509,f184])).
% 5.24/1.00  fof(f5317,plain,(
% 5.24/1.00    spl7_79 | ~spl7_3 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f514,f507,f84,f5314])).
% 5.24/1.00  fof(f5314,plain,(
% 5.24/1.00    spl7_79 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k3_xboole_0(sK1,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).
% 5.24/1.00  fof(f514,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k3_xboole_0(sK1,sK1))) | (~spl7_3 | ~spl7_26)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f86,f509,f184])).
% 5.24/1.00  fof(f4682,plain,(
% 5.24/1.00    spl7_78 | ~spl7_5 | ~spl7_20),
% 5.24/1.00    inference(avatar_split_clause,[],[f478,f326,f116,f4679])).
% 5.24/1.00  fof(f4679,plain,(
% 5.24/1.00    spl7_78 <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 5.24/1.00  fof(f326,plain,(
% 5.24/1.00    spl7_20 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 5.24/1.00  fof(f478,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))))) | (~spl7_5 | ~spl7_20)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f328,f118,f184])).
% 5.24/1.00  fof(f328,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))))) | ~spl7_20),
% 5.24/1.00    inference(avatar_component_clause,[],[f326])).
% 5.24/1.00  fof(f4677,plain,(
% 5.24/1.00    spl7_77 | ~spl7_5 | ~spl7_20),
% 5.24/1.00    inference(avatar_split_clause,[],[f472,f326,f116,f4674])).
% 5.24/1.00  fof(f4674,plain,(
% 5.24/1.00    spl7_77 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).
% 5.24/1.00  fof(f472,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),sK1)) | (~spl7_5 | ~spl7_20)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f328,f184])).
% 5.24/1.00  fof(f4433,plain,(
% 5.24/1.00    spl7_76 | ~spl7_1 | ~spl7_68),
% 5.24/1.00    inference(avatar_split_clause,[],[f3903,f3396,f74,f4430])).
% 5.24/1.00  fof(f4430,plain,(
% 5.24/1.00    spl7_76 <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).
% 5.24/1.00  fof(f3396,plain,(
% 5.24/1.00    spl7_68 <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 5.24/1.00  fof(f3903,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2)) | (~spl7_1 | ~spl7_68)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f3398,f64])).
% 5.24/1.00  fof(f3398,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl7_68),
% 5.24/1.00    inference(avatar_component_clause,[],[f3396])).
% 5.24/1.00  fof(f4428,plain,(
% 5.24/1.00    spl7_75 | ~spl7_1 | ~spl7_67),
% 5.24/1.00    inference(avatar_split_clause,[],[f3796,f3019,f74,f4425])).
% 5.24/1.00  fof(f4425,plain,(
% 5.24/1.00    spl7_75 <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 5.24/1.00  fof(f3019,plain,(
% 5.24/1.00    spl7_67 <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 5.24/1.00  fof(f3796,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(sK2)) | (~spl7_1 | ~spl7_67)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f3021,f64])).
% 5.24/1.00  fof(f3021,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl7_67),
% 5.24/1.00    inference(avatar_component_clause,[],[f3019])).
% 5.24/1.00  fof(f4257,plain,(
% 5.24/1.00    spl7_74 | ~spl7_6 | ~spl7_11),
% 5.24/1.00    inference(avatar_split_clause,[],[f442,f188,f122,f4254])).
% 5.24/1.00  fof(f4254,plain,(
% 5.24/1.00    spl7_74 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 5.24/1.00  fof(f188,plain,(
% 5.24/1.00    spl7_11 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 5.24/1.00  fof(f442,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),k1_relat_1(sK2))) | (~spl7_6 | ~spl7_11)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f190,f184])).
% 5.24/1.00  fof(f190,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))) | ~spl7_11),
% 5.24/1.00    inference(avatar_component_clause,[],[f188])).
% 5.24/1.00  fof(f4249,plain,(
% 5.24/1.00    spl7_73 | ~spl7_70),
% 5.24/1.00    inference(avatar_split_clause,[],[f3982,f3893,f4246])).
% 5.24/1.00  fof(f3893,plain,(
% 5.24/1.00    spl7_70 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k2_relat_1(sK6(sK1,sK0)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 5.24/1.00  fof(f3982,plain,(
% 5.24/1.00    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) | ~spl7_70),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f3895,f1606])).
% 5.24/1.00  fof(f1606,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X5,k2_relat_1(sK6(X3,X4))) | X4 = X5) )),
% 5.24/1.00    inference(subsumption_resolution,[],[f1602,f156])).
% 5.24/1.00  fof(f156,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (r2_hidden(sK5(sK6(X4,X5),X3),X4) | ~r2_hidden(X3,k2_relat_1(sK6(X4,X5)))) )),
% 5.24/1.00    inference(forward_demodulation,[],[f155,f61])).
% 5.24/1.00  fof(f155,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_relat_1(sK6(X4,X5))) | r2_hidden(sK5(sK6(X4,X5),X3),k1_relat_1(sK6(X4,X5)))) )),
% 5.24/1.00    inference(subsumption_resolution,[],[f150,f59])).
% 5.24/1.00  fof(f150,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_relat_1(sK6(X4,X5))) | r2_hidden(sK5(sK6(X4,X5),X3),k1_relat_1(sK6(X4,X5))) | ~v1_relat_1(sK6(X4,X5))) )),
% 5.24/1.00    inference(resolution,[],[f72,f60])).
% 5.24/1.00  fof(f1602,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (X4 = X5 | ~r2_hidden(X5,k2_relat_1(sK6(X3,X4))) | ~r2_hidden(sK5(sK6(X3,X4),X5),X3)) )),
% 5.24/1.00    inference(superposition,[],[f252,f62])).
% 5.24/1.00  fof(f252,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (k1_funct_1(sK6(X4,X5),sK5(sK6(X4,X5),X3)) = X3 | ~r2_hidden(X3,k2_relat_1(sK6(X4,X5)))) )),
% 5.24/1.00    inference(subsumption_resolution,[],[f247,f59])).
% 5.24/1.00  fof(f247,plain,(
% 5.24/1.00    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_relat_1(sK6(X4,X5))) | k1_funct_1(sK6(X4,X5),sK5(sK6(X4,X5),X3)) = X3 | ~v1_relat_1(sK6(X4,X5))) )),
% 5.24/1.00    inference(resolution,[],[f71,f60])).
% 5.24/1.00  fof(f3895,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k2_relat_1(sK6(sK1,sK0))) | ~spl7_70),
% 5.24/1.00    inference(avatar_component_clause,[],[f3893])).
% 5.24/1.00  fof(f3933,plain,(
% 5.24/1.00    spl7_72 | ~spl7_1 | ~spl7_68),
% 5.24/1.00    inference(avatar_split_clause,[],[f3904,f3396,f74,f3930])).
% 5.24/1.00  fof(f3930,plain,(
% 5.24/1.00    spl7_72 <=> r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 5.24/1.00  fof(f3904,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1) | (~spl7_1 | ~spl7_68)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f3398,f63])).
% 5.24/1.00  fof(f63,plain,(
% 5.24/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 5.24/1.00    inference(cnf_transformation,[],[f38])).
% 5.24/1.00  fof(f3901,plain,(
% 5.24/1.00    spl7_71 | ~spl7_1 | ~spl7_2 | ~spl7_54),
% 5.24/1.00    inference(avatar_split_clause,[],[f2555,f2531,f79,f74,f3898])).
% 5.24/1.00  fof(f3898,plain,(
% 5.24/1.00    spl7_71 <=> r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)),k2_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 5.24/1.00  fof(f2531,plain,(
% 5.24/1.00    spl7_54 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 5.24/1.00  fof(f2555,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)),k2_relat_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_54)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f81,f2533,f70])).
% 5.24/1.00  fof(f2533,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(sK2)) | ~spl7_54),
% 5.24/1.00    inference(avatar_component_clause,[],[f2531])).
% 5.24/1.00  fof(f3896,plain,(
% 5.24/1.00    spl7_70 | ~spl7_41),
% 5.24/1.00    inference(avatar_split_clause,[],[f1541,f1466,f3893])).
% 5.24/1.00  fof(f1466,plain,(
% 5.24/1.00    spl7_41 <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 5.24/1.00  fof(f1541,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k2_relat_1(sK6(sK1,sK0))) | ~spl7_41),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f1468,f285])).
% 5.24/1.00  fof(f1468,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),sK1)) | ~spl7_41),
% 5.24/1.00    inference(avatar_component_clause,[],[f1466])).
% 5.24/1.00  fof(f3891,plain,(
% 5.24/1.00    spl7_69 | ~spl7_40),
% 5.24/1.00    inference(avatar_split_clause,[],[f1486,f1461,f3888])).
% 5.24/1.00  fof(f3888,plain,(
% 5.24/1.00    spl7_69 <=> r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK6(sK1,sK0))),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 5.24/1.00  fof(f1461,plain,(
% 5.24/1.00    spl7_40 <=> r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(sK1,sK0))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 5.24/1.00  fof(f1486,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK6(sK1,sK0))),sK0),sK1) | ~spl7_40),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f1463,f285])).
% 5.24/1.00  fof(f1463,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(sK1,sK0)))) | ~spl7_40),
% 5.24/1.00    inference(avatar_component_clause,[],[f1461])).
% 5.24/1.00  fof(f3399,plain,(
% 5.24/1.00    spl7_68 | ~spl7_3),
% 5.24/1.00    inference(avatar_split_clause,[],[f202,f84,f3396])).
% 5.24/1.00  fof(f202,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl7_3),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f86,f154])).
% 5.24/1.00  fof(f3022,plain,(
% 5.24/1.00    spl7_67 | ~spl7_3),
% 5.24/1.00    inference(avatar_split_clause,[],[f143,f84,f3019])).
% 5.24/1.00  fof(f143,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl7_3),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f86,f134])).
% 5.24/1.00  fof(f3017,plain,(
% 5.24/1.00    spl7_66 | ~spl7_38),
% 5.24/1.00    inference(avatar_split_clause,[],[f1297,f817,f3014])).
% 5.24/1.00  fof(f3014,plain,(
% 5.24/1.00    spl7_66 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 5.24/1.00  fof(f817,plain,(
% 5.24/1.00    spl7_38 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 5.24/1.00  fof(f1297,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,k1_relat_1(sK2))) | ~spl7_38),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f819,f285])).
% 5.24/1.00  fof(f819,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),sK1)) | ~spl7_38),
% 5.24/1.00    inference(avatar_component_clause,[],[f817])).
% 5.24/1.00  fof(f3012,plain,(
% 5.24/1.00    spl7_65 | ~spl7_37),
% 5.24/1.00    inference(avatar_split_clause,[],[f1248,f812,f3009])).
% 5.24/1.00  fof(f3009,plain,(
% 5.24/1.00    spl7_65 <=> r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(sK2))),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 5.24/1.00  fof(f812,plain,(
% 5.24/1.00    spl7_37 <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(sK2))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 5.24/1.00  fof(f1248,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(sK2))),sK0),sK1) | ~spl7_37),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f814,f285])).
% 5.24/1.00  fof(f814,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(sK2)))) | ~spl7_37),
% 5.24/1.00    inference(avatar_component_clause,[],[f812])).
% 5.24/1.00  fof(f2980,plain,(
% 5.24/1.00    spl7_64 | ~spl7_5 | ~spl7_23),
% 5.24/1.00    inference(avatar_split_clause,[],[f1113,f347,f116,f2977])).
% 5.24/1.00  fof(f2977,plain,(
% 5.24/1.00    spl7_64 <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k2_relat_1(sK2),sK0)),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 5.24/1.00  fof(f347,plain,(
% 5.24/1.00    spl7_23 <=> r2_hidden(sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 5.24/1.00  fof(f1113,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k2_relat_1(sK2),sK0)),sK1)) | (~spl7_5 | ~spl7_23)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f862,f184])).
% 5.24/1.00  fof(f862,plain,(
% 5.24/1.00    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(k2_relat_1(sK2),X0)))) ) | ~spl7_23),
% 5.24/1.00    inference(forward_demodulation,[],[f845,f402])).
% 5.24/1.00  fof(f402,plain,(
% 5.24/1.00    ( ! [X0] : (k1_funct_1(sK6(k2_relat_1(sK2),X0),sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0))) = X0) ) | ~spl7_23),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f349,f62])).
% 5.24/1.00  fof(f349,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2)) | ~spl7_23),
% 5.24/1.00    inference(avatar_component_clause,[],[f347])).
% 5.24/1.00  fof(f845,plain,(
% 5.24/1.00    ( ! [X0] : (r2_hidden(k1_funct_1(sK6(k2_relat_1(sK2),X0),sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0))),k2_relat_1(sK6(k2_relat_1(sK2),X0)))) ) | ~spl7_23),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f349,f136])).
% 5.24/1.00  fof(f2975,plain,(
% 5.24/1.00    spl7_63 | ~spl7_5 | ~spl7_23),
% 5.24/1.00    inference(avatar_split_clause,[],[f1081,f347,f116,f2972])).
% 5.24/1.00  fof(f2972,plain,(
% 5.24/1.00    spl7_63 <=> r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k2_relat_1(sK2),sK0))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 5.24/1.00  fof(f1081,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k2_relat_1(sK2),sK0)))) | (~spl7_5 | ~spl7_23)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f862,f184])).
% 5.24/1.00  fof(f2819,plain,(
% 5.24/1.00    spl7_62 | ~spl7_1 | ~spl7_6 | ~spl7_17),
% 5.24/1.00    inference(avatar_split_clause,[],[f965,f270,f122,f74,f2816])).
% 5.24/1.00  fof(f2816,plain,(
% 5.24/1.00    spl7_62 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(sK1,sK0)))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 5.24/1.00  fof(f270,plain,(
% 5.24/1.00    spl7_17 <=> r2_hidden(sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 5.24/1.00  fof(f965,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK6(sK1,sK0))))) | (~spl7_1 | ~spl7_6 | ~spl7_17)),
% 5.24/1.00    inference(forward_demodulation,[],[f911,f97])).
% 5.24/1.00  fof(f911,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),k2_relat_1(sK6(sK1,sK0)))) | (~spl7_6 | ~spl7_17)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f858,f184])).
% 5.24/1.00  fof(f858,plain,(
% 5.24/1.00    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(sK1,X0)))) ) | ~spl7_17),
% 5.24/1.00    inference(forward_demodulation,[],[f849,f295])).
% 5.24/1.00  fof(f295,plain,(
% 5.24/1.00    ( ! [X0] : (k1_funct_1(sK6(sK1,X0),sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0))) = X0) ) | ~spl7_17),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f272,f62])).
% 5.24/1.00  fof(f272,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1) | ~spl7_17),
% 5.24/1.00    inference(avatar_component_clause,[],[f270])).
% 5.24/1.00  fof(f849,plain,(
% 5.24/1.00    ( ! [X0] : (r2_hidden(k1_funct_1(sK6(sK1,X0),sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0))),k2_relat_1(sK6(sK1,X0)))) ) | ~spl7_17),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f272,f136])).
% 5.24/1.00  fof(f2814,plain,(
% 5.24/1.00    spl7_61 | ~spl7_6 | ~spl7_17),
% 5.24/1.00    inference(avatar_split_clause,[],[f941,f270,f122,f2811])).
% 5.24/1.00  fof(f2811,plain,(
% 5.24/1.00    spl7_61 <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 5.24/1.00  fof(f941,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),k1_relat_1(sK2))) | (~spl7_6 | ~spl7_17)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f858,f184])).
% 5.24/1.00  fof(f2809,plain,(
% 5.24/1.00    spl7_60 | ~spl7_30),
% 5.24/1.00    inference(avatar_split_clause,[],[f643,f579,f2806])).
% 5.24/1.00  fof(f2806,plain,(
% 5.24/1.00    spl7_60 <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k3_xboole_0(sK1,sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 5.24/1.00  fof(f579,plain,(
% 5.24/1.00    spl7_30 <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 5.24/1.00  fof(f643,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k3_xboole_0(sK1,sK1)) | ~spl7_30),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f581,f581,f184])).
% 5.24/1.00  fof(f581,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),sK1) | ~spl7_30),
% 5.24/1.00    inference(avatar_component_clause,[],[f579])).
% 5.24/1.00  fof(f2804,plain,(
% 5.24/1.00    spl7_59 | ~spl7_5 | ~spl7_29),
% 5.24/1.00    inference(avatar_split_clause,[],[f631,f574,f116,f2801])).
% 5.24/1.00  fof(f2801,plain,(
% 5.24/1.00    spl7_59 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK1),sK1),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 5.24/1.00  fof(f574,plain,(
% 5.24/1.00    spl7_29 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 5.24/1.00  fof(f631,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK1),sK1),sK1)) | (~spl7_5 | ~spl7_29)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f576,f184])).
% 5.24/1.00  fof(f576,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) | ~spl7_29),
% 5.24/1.00    inference(avatar_component_clause,[],[f574])).
% 5.24/1.00  fof(f2799,plain,(
% 5.24/1.00    spl7_58 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f751,f122,f2796])).
% 5.24/1.00  fof(f2796,plain,(
% 5.24/1.00    spl7_58 <=> sK0 = k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK5(k6_relat_1(k1_relat_1(sK2)),sK0))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 5.24/1.00  fof(f751,plain,(
% 5.24/1.00    sK0 = k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK5(k6_relat_1(k1_relat_1(sK2)),sK0)) | ~spl7_6),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f251])).
% 5.24/1.00  fof(f2794,plain,(
% 5.24/1.00    spl7_57 | ~spl7_5 | ~spl7_29),
% 5.24/1.00    inference(avatar_split_clause,[],[f620,f574,f116,f2791])).
% 5.24/1.00  fof(f2791,plain,(
% 5.24/1.00    spl7_57 <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 5.24/1.00  fof(f620,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))) | (~spl7_5 | ~spl7_29)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f576,f184])).
% 5.24/1.00  fof(f2789,plain,(
% 5.24/1.00    spl7_56 | ~spl7_5 | ~spl7_28),
% 5.24/1.00    inference(avatar_split_clause,[],[f602,f569,f116,f2786])).
% 5.24/1.00  fof(f2786,plain,(
% 5.24/1.00    spl7_56 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 5.24/1.00  fof(f569,plain,(
% 5.24/1.00    spl7_28 <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 5.24/1.00  fof(f602,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)),sK1)) | (~spl7_5 | ~spl7_28)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f571,f184])).
% 5.24/1.00  fof(f571,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))) | ~spl7_28),
% 5.24/1.00    inference(avatar_component_clause,[],[f569])).
% 5.24/1.00  fof(f2784,plain,(
% 5.24/1.00    spl7_55 | ~spl7_5 | ~spl7_28),
% 5.24/1.00    inference(avatar_split_clause,[],[f592,f569,f116,f2781])).
% 5.24/1.00  fof(f2781,plain,(
% 5.24/1.00    spl7_55 <=> r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 5.24/1.00  fof(f592,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))) | (~spl7_5 | ~spl7_28)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f571,f184])).
% 5.24/1.00  fof(f2534,plain,(
% 5.24/1.00    spl7_54 | ~spl7_1 | ~spl7_50),
% 5.24/1.00    inference(avatar_split_clause,[],[f2503,f2077,f74,f2531])).
% 5.24/1.00  fof(f2077,plain,(
% 5.24/1.00    spl7_50 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK2,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 5.24/1.00  fof(f2503,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(sK2)) | (~spl7_1 | ~spl7_50)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f2079,f64])).
% 5.24/1.00  fof(f2079,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl7_50),
% 5.24/1.00    inference(avatar_component_clause,[],[f2077])).
% 5.24/1.00  fof(f2220,plain,(
% 5.24/1.00    spl7_53 | ~spl7_5 | ~spl7_13),
% 5.24/1.00    inference(avatar_split_clause,[],[f1027,f229,f116,f2217])).
% 5.24/1.00  fof(f2217,plain,(
% 5.24/1.00    spl7_53 <=> r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 5.24/1.00  fof(f1027,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(k1_relat_1(sK2),sK0)),sK1)) | (~spl7_5 | ~spl7_13)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f863,f184])).
% 5.24/1.00  fof(f2215,plain,(
% 5.24/1.00    spl7_52 | ~spl7_5 | ~spl7_13),
% 5.24/1.00    inference(avatar_split_clause,[],[f996,f229,f116,f2212])).
% 5.24/1.00  fof(f2212,plain,(
% 5.24/1.00    spl7_52 <=> r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k1_relat_1(sK2),sK0))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 5.24/1.00  fof(f996,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(k1_relat_1(sK2),sK0)))) | (~spl7_5 | ~spl7_13)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f863,f184])).
% 5.24/1.00  fof(f2085,plain,(
% 5.24/1.00    spl7_51 | ~spl7_32),
% 5.24/1.00    inference(avatar_split_clause,[],[f703,f656,f2082])).
% 5.24/1.00  fof(f2082,plain,(
% 5.24/1.00    spl7_51 <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 5.24/1.00  fof(f703,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),sK0),sK1) | ~spl7_32),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f658,f285])).
% 5.24/1.00  fof(f2080,plain,(
% 5.24/1.00    spl7_50 | ~spl7_31),
% 5.24/1.00    inference(avatar_split_clause,[],[f670,f651,f2077])).
% 5.24/1.00  fof(f670,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl7_31),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f653,f285])).
% 5.24/1.00  fof(f2075,plain,(
% 5.24/1.00    spl7_49 | ~spl7_1 | ~spl7_6 | ~spl7_27),
% 5.24/1.00    inference(avatar_split_clause,[],[f564,f538,f122,f74,f2072])).
% 5.24/1.00  fof(f2072,plain,(
% 5.24/1.00    spl7_49 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,k1_relat_1(sK2)))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 5.24/1.00  fof(f564,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,k1_relat_1(sK2))))) | (~spl7_1 | ~spl7_6 | ~spl7_27)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f124,f540,f65])).
% 5.24/1.00  fof(f2070,plain,(
% 5.24/1.00    spl7_48 | ~spl7_6 | ~spl7_27),
% 5.24/1.00    inference(avatar_split_clause,[],[f558,f538,f122,f2067])).
% 5.24/1.00  fof(f2067,plain,(
% 5.24/1.00    spl7_48 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 5.24/1.00  fof(f558,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),k1_relat_1(sK2))) | (~spl7_6 | ~spl7_27)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f540,f184])).
% 5.24/1.00  fof(f2049,plain,(
% 5.24/1.00    spl7_47 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f529,f507,f2046])).
% 5.24/1.00  fof(f2046,plain,(
% 5.24/1.00    spl7_47 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK1)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 5.24/1.00  fof(f529,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK1))) | ~spl7_26),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f509,f509,f184])).
% 5.24/1.00  fof(f1823,plain,(
% 5.24/1.00    spl7_46 | ~spl7_7),
% 5.24/1.00    inference(avatar_split_clause,[],[f480,f138,f1820])).
% 5.24/1.00  fof(f1820,plain,(
% 5.24/1.00    spl7_46 <=> r2_hidden(k1_funct_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 5.24/1.00  fof(f138,plain,(
% 5.24/1.00    spl7_7 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 5.24/1.00  fof(f480,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))) | ~spl7_7),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f140,f140,f184])).
% 5.24/1.00  fof(f140,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~spl7_7),
% 5.24/1.00    inference(avatar_component_clause,[],[f138])).
% 5.24/1.00  fof(f1818,plain,(
% 5.24/1.00    spl7_45 | ~spl7_5 | ~spl7_11),
% 5.24/1.00    inference(avatar_split_clause,[],[f474,f188,f116,f1815])).
% 5.24/1.00  fof(f474,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))) | (~spl7_5 | ~spl7_11)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f190,f118,f184])).
% 5.24/1.00  fof(f1813,plain,(
% 5.24/1.00    spl7_44 | ~spl7_5 | ~spl7_11),
% 5.24/1.00    inference(avatar_split_clause,[],[f444,f188,f116,f1810])).
% 5.24/1.00  fof(f1810,plain,(
% 5.24/1.00    spl7_44 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 5.24/1.00  fof(f444,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))),sK1)) | (~spl7_5 | ~spl7_11)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f190,f184])).
% 5.24/1.00  fof(f1808,plain,(
% 5.24/1.00    spl7_43 | ~spl7_3 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f435,f122,f84,f1805])).
% 5.24/1.00  fof(f1805,plain,(
% 5.24/1.00    spl7_43 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 5.24/1.00  fof(f435,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))) | (~spl7_3 | ~spl7_6)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f86,f184])).
% 5.24/1.00  fof(f1611,plain,(
% 5.24/1.00    spl7_42 | ~spl7_5),
% 5.24/1.00    inference(avatar_split_clause,[],[f753,f116,f1608])).
% 5.24/1.00  fof(f1608,plain,(
% 5.24/1.00    spl7_42 <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 5.24/1.00  fof(f753,plain,(
% 5.24/1.00    sK0 = k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)) | ~spl7_5),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f251])).
% 5.24/1.00  fof(f1469,plain,(
% 5.24/1.00    spl7_41 | ~spl7_5 | ~spl7_17),
% 5.24/1.00    inference(avatar_split_clause,[],[f943,f270,f116,f1466])).
% 5.24/1.00  fof(f943,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k2_relat_1(sK6(sK1,sK0)),sK1)) | (~spl7_5 | ~spl7_17)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f858,f184])).
% 5.24/1.00  fof(f1464,plain,(
% 5.24/1.00    spl7_40 | ~spl7_5 | ~spl7_17),
% 5.24/1.00    inference(avatar_split_clause,[],[f913,f270,f116,f1461])).
% 5.24/1.00  fof(f913,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k2_relat_1(sK6(sK1,sK0)))) | (~spl7_5 | ~spl7_17)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f858,f184])).
% 5.24/1.00  fof(f1451,plain,(
% 5.24/1.00    spl7_39 | ~spl7_28),
% 5.24/1.00    inference(avatar_split_clause,[],[f583,f569,f1448])).
% 5.24/1.00  fof(f1448,plain,(
% 5.24/1.00    spl7_39 <=> r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 5.24/1.00  fof(f583,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k3_xboole_0(sK1,sK1)),sK0),sK1) | ~spl7_28),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f571,f285])).
% 5.24/1.00  fof(f820,plain,(
% 5.24/1.00    spl7_38 | ~spl7_5 | ~spl7_27),
% 5.24/1.00    inference(avatar_split_clause,[],[f560,f538,f116,f817])).
% 5.24/1.00  fof(f560,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)),sK1)) | (~spl7_5 | ~spl7_27)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f540,f184])).
% 5.24/1.00  fof(f815,plain,(
% 5.24/1.00    spl7_37 | ~spl7_5 | ~spl7_27),
% 5.24/1.00    inference(avatar_split_clause,[],[f551,f538,f116,f812])).
% 5.24/1.00  fof(f551,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,k1_relat_1(sK2)))) | (~spl7_5 | ~spl7_27)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f540,f184])).
% 5.24/1.00  fof(f810,plain,(
% 5.24/1.00    spl7_36 | ~spl7_1 | ~spl7_6 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f531,f507,f122,f74,f807])).
% 5.24/1.00  fof(f807,plain,(
% 5.24/1.00    spl7_36 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,sK1))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 5.24/1.00  fof(f531,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(sK1,sK1)))) | (~spl7_1 | ~spl7_6 | ~spl7_26)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f124,f509,f65])).
% 5.24/1.00  fof(f805,plain,(
% 5.24/1.00    spl7_35 | ~spl7_6 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f526,f507,f122,f802])).
% 5.24/1.00  fof(f802,plain,(
% 5.24/1.00    spl7_35 <=> r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(sK2)))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 5.24/1.00  fof(f526,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),k1_relat_1(sK2))) | (~spl7_6 | ~spl7_26)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f509,f184])).
% 5.24/1.00  fof(f669,plain,(
% 5.24/1.00    spl7_34 | ~spl7_12),
% 5.24/1.00    inference(avatar_split_clause,[],[f490,f211,f666])).
% 5.24/1.00  fof(f490,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1)) | ~spl7_12),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f213,f213,f184])).
% 5.24/1.00  fof(f664,plain,(
% 5.24/1.00    spl7_33 | ~spl7_8),
% 5.24/1.00    inference(avatar_split_clause,[],[f481,f158,f661])).
% 5.24/1.00  fof(f661,plain,(
% 5.24/1.00    spl7_33 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 5.24/1.00  fof(f158,plain,(
% 5.24/1.00    spl7_8 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 5.24/1.00  fof(f481,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),k3_xboole_0(sK1,sK1)) | ~spl7_8),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f160,f160,f184])).
% 5.24/1.00  fof(f160,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),sK1) | ~spl7_8),
% 5.24/1.00    inference(avatar_component_clause,[],[f158])).
% 5.24/1.00  fof(f659,plain,(
% 5.24/1.00    spl7_32 | ~spl7_3 | ~spl7_5),
% 5.24/1.00    inference(avatar_split_clause,[],[f473,f116,f84,f656])).
% 5.24/1.00  fof(f473,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1)))) | (~spl7_3 | ~spl7_5)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f86,f118,f184])).
% 5.24/1.00  fof(f654,plain,(
% 5.24/1.00    spl7_31 | ~spl7_3 | ~spl7_5),
% 5.24/1.00    inference(avatar_split_clause,[],[f437,f116,f84,f651])).
% 5.24/1.00  fof(f437,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),sK1)) | (~spl7_3 | ~spl7_5)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f86,f184])).
% 5.24/1.00  fof(f582,plain,(
% 5.24/1.00    spl7_30 | ~spl7_27),
% 5.24/1.00    inference(avatar_split_clause,[],[f542,f538,f579])).
% 5.24/1.00  fof(f542,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),sK1) | ~spl7_27),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f540,f285])).
% 5.24/1.00  fof(f577,plain,(
% 5.24/1.00    spl7_29 | ~spl7_5 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f528,f507,f116,f574])).
% 5.24/1.00  fof(f528,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) | (~spl7_5 | ~spl7_26)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f509,f184])).
% 5.24/1.00  fof(f572,plain,(
% 5.24/1.00    spl7_28 | ~spl7_5 | ~spl7_26),
% 5.24/1.00    inference(avatar_split_clause,[],[f520,f507,f116,f569])).
% 5.24/1.00  fof(f520,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))) | (~spl7_5 | ~spl7_26)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f509,f184])).
% 5.24/1.00  fof(f541,plain,(
% 5.24/1.00    spl7_27 | ~spl7_5 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f477,f122,f116,f538])).
% 5.24/1.00  fof(f477,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) | (~spl7_5 | ~spl7_6)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f118,f184])).
% 5.24/1.00  fof(f510,plain,(
% 5.24/1.00    spl7_26 | ~spl7_5),
% 5.24/1.00    inference(avatar_split_clause,[],[f479,f116,f507])).
% 5.24/1.00  fof(f479,plain,(
% 5.24/1.00    r2_hidden(sK0,k3_xboole_0(sK1,sK1)) | ~spl7_5),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f118,f184])).
% 5.24/1.00  fof(f430,plain,(
% 5.24/1.00    spl7_25 | ~spl7_1 | ~spl7_2 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f376,f122,f79,f74,f427])).
% 5.24/1.00  fof(f427,plain,(
% 5.24/1.00    spl7_25 <=> k1_funct_1(k5_relat_1(sK2,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK2,sK0))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 5.24/1.00  fof(f376,plain,(
% 5.24/1.00    k1_funct_1(k5_relat_1(sK2,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK2,sK0)) | (~spl7_1 | ~spl7_2 | ~spl7_6)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f81,f76,f81,f124,f58])).
% 5.24/1.00  fof(f355,plain,(
% 5.24/1.00    spl7_24 | ~spl7_1 | ~spl7_2 | ~spl7_13),
% 5.24/1.00    inference(avatar_split_clause,[],[f234,f229,f79,f74,f352])).
% 5.24/1.00  fof(f352,plain,(
% 5.24/1.00    spl7_24 <=> r2_hidden(k1_funct_1(sK2,sK5(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 5.24/1.00  fof(f234,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(sK2,sK5(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_13)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f81,f231,f70])).
% 5.24/1.00  fof(f350,plain,(
% 5.24/1.00    spl7_23 | ~spl7_7),
% 5.24/1.00    inference(avatar_split_clause,[],[f206,f138,f347])).
% 5.24/1.00  fof(f206,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2)) | ~spl7_7),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f140,f154])).
% 5.24/1.00  fof(f345,plain,(
% 5.24/1.00    spl7_22 | ~spl7_1 | ~spl7_6 | ~spl7_11),
% 5.24/1.00    inference(avatar_split_clause,[],[f194,f188,f122,f74,f342])).
% 5.24/1.00  fof(f342,plain,(
% 5.24/1.00    spl7_22 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 5.24/1.00  fof(f194,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))))) | (~spl7_1 | ~spl7_6 | ~spl7_11)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f124,f190,f65])).
% 5.24/1.00  fof(f340,plain,(
% 5.24/1.00    spl7_21 | ~spl7_1 | ~spl7_2 | ~spl7_9),
% 5.24/1.00    inference(avatar_split_clause,[],[f169,f165,f79,f74,f337])).
% 5.24/1.00  fof(f337,plain,(
% 5.24/1.00    spl7_21 <=> r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 5.24/1.00  fof(f165,plain,(
% 5.24/1.00    spl7_9 <=> r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 5.24/1.00  fof(f169,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(sK2,k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0)),k2_relat_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_9)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f81,f167,f70])).
% 5.24/1.00  fof(f167,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2)) | ~spl7_9),
% 5.24/1.00    inference(avatar_component_clause,[],[f165])).
% 5.24/1.00  fof(f329,plain,(
% 5.24/1.00    spl7_20 | ~spl7_1 | ~spl7_2 | ~spl7_6 | ~spl7_7),
% 5.24/1.00    inference(avatar_split_clause,[],[f313,f138,f122,f79,f74,f326])).
% 5.24/1.00  fof(f313,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))))) | (~spl7_1 | ~spl7_2 | ~spl7_6 | ~spl7_7)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f81,f124,f140,f68])).
% 5.24/1.00  fof(f68,plain,(
% 5.24/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 5.24/1.00    inference(cnf_transformation,[],[f40])).
% 5.24/1.00  fof(f312,plain,(
% 5.24/1.00    spl7_19 | ~spl7_7),
% 5.24/1.00    inference(avatar_split_clause,[],[f146,f138,f309])).
% 5.24/1.00  fof(f309,plain,(
% 5.24/1.00    spl7_19 <=> r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 5.24/1.00  fof(f146,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k2_relat_1(sK2)),k1_funct_1(sK2,sK0)),k2_relat_1(sK2)) | ~spl7_7),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f140,f134])).
% 5.24/1.00  fof(f278,plain,(
% 5.24/1.00    spl7_18 | ~spl7_12),
% 5.24/1.00    inference(avatar_split_clause,[],[f226,f211,f275])).
% 5.24/1.00  fof(f275,plain,(
% 5.24/1.00    spl7_18 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 5.24/1.00  fof(f226,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1) | ~spl7_12),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f213,f134])).
% 5.24/1.00  fof(f273,plain,(
% 5.24/1.00    spl7_17 | ~spl7_12),
% 5.24/1.00    inference(avatar_split_clause,[],[f225,f211,f270])).
% 5.24/1.00  fof(f225,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK5(k6_relat_1(sK1),sK0)),sK1) | ~spl7_12),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f213,f154])).
% 5.24/1.00  fof(f268,plain,(
% 5.24/1.00    spl7_16 | ~spl7_8),
% 5.24/1.00    inference(avatar_split_clause,[],[f207,f158,f265])).
% 5.24/1.00  fof(f265,plain,(
% 5.24/1.00    spl7_16 <=> r2_hidden(sK5(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 5.24/1.00  fof(f207,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1) | ~spl7_8),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f160,f154])).
% 5.24/1.00  fof(f263,plain,(
% 5.24/1.00    spl7_15 | ~spl7_8),
% 5.24/1.00    inference(avatar_split_clause,[],[f162,f158,f260])).
% 5.24/1.00  fof(f260,plain,(
% 5.24/1.00    spl7_15 <=> r2_hidden(k1_funct_1(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1)),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 5.24/1.00  fof(f162,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),k1_funct_1(k6_relat_1(sK1),sK0)),sK1) | ~spl7_8),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f160,f134])).
% 5.24/1.00  fof(f243,plain,(
% 5.24/1.00    spl7_14 | ~spl7_1 | ~spl7_3 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f177,f122,f84,f74,f240])).
% 5.24/1.00  fof(f240,plain,(
% 5.24/1.00    spl7_14 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK1)))))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 5.24/1.00  fof(f177,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK1))))) | (~spl7_1 | ~spl7_3 | ~spl7_6)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f86,f124,f65])).
% 5.24/1.00  fof(f232,plain,(
% 5.24/1.00    spl7_13 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f204,f122,f229])).
% 5.24/1.00  fof(f204,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2)) | ~spl7_6),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f154])).
% 5.24/1.00  fof(f214,plain,(
% 5.24/1.00    spl7_12 | ~spl7_5),
% 5.24/1.00    inference(avatar_split_clause,[],[f205,f116,f211])).
% 5.24/1.00  fof(f205,plain,(
% 5.24/1.00    r2_hidden(sK5(k6_relat_1(sK1),sK0),sK1) | ~spl7_5),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f154])).
% 5.24/1.00  fof(f191,plain,(
% 5.24/1.00    spl7_11 | ~spl7_1 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f178,f122,f74,f188])).
% 5.24/1.00  fof(f178,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))) | (~spl7_1 | ~spl7_6)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f124,f124,f65])).
% 5.24/1.00  fof(f176,plain,(
% 5.24/1.00    spl7_10 | ~spl7_1 | ~spl7_2 | ~spl7_7),
% 5.24/1.00    inference(avatar_split_clause,[],[f147,f138,f79,f74,f173])).
% 5.24/1.00  fof(f173,plain,(
% 5.24/1.00    spl7_10 <=> r2_hidden(sK5(sK2,k1_funct_1(sK2,sK0)),k1_relat_1(sK2))),
% 5.24/1.00    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 5.24/1.00  fof(f147,plain,(
% 5.24/1.00    r2_hidden(sK5(sK2,k1_funct_1(sK2,sK0)),k1_relat_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f81,f140,f72])).
% 5.24/1.00  fof(f168,plain,(
% 5.24/1.00    spl7_9 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f144,f122,f165])).
% 5.24/1.00  fof(f144,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(k1_relat_1(sK2)),sK0),k1_relat_1(sK2)) | ~spl7_6),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f124,f134])).
% 5.24/1.00  fof(f161,plain,(
% 5.24/1.00    spl7_8 | ~spl7_5),
% 5.24/1.00    inference(avatar_split_clause,[],[f145,f116,f158])).
% 5.24/1.00  fof(f145,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(k6_relat_1(sK1),sK0),sK1) | ~spl7_5),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f118,f134])).
% 5.24/1.00  fof(f141,plain,(
% 5.24/1.00    spl7_7 | ~spl7_1 | ~spl7_2 | ~spl7_6),
% 5.24/1.00    inference(avatar_split_clause,[],[f127,f122,f79,f74,f138])).
% 5.24/1.00  fof(f127,plain,(
% 5.24/1.00    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_6)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f81,f124,f70])).
% 5.24/1.00  fof(f125,plain,(
% 5.24/1.00    spl7_6 | ~spl7_1 | ~spl7_3),
% 5.24/1.00    inference(avatar_split_clause,[],[f107,f84,f74,f122])).
% 5.24/1.00  fof(f107,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(sK2)) | (~spl7_1 | ~spl7_3)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f86,f64])).
% 5.24/1.00  fof(f119,plain,(
% 5.24/1.00    spl7_5 | ~spl7_1 | ~spl7_3),
% 5.24/1.00    inference(avatar_split_clause,[],[f106,f84,f74,f116])).
% 5.24/1.00  fof(f106,plain,(
% 5.24/1.00    r2_hidden(sK0,sK1) | (~spl7_1 | ~spl7_3)),
% 5.24/1.00    inference(unit_resulting_resolution,[],[f76,f86,f63])).
% 5.24/1.00  fof(f92,plain,(
% 5.24/1.00    ~spl7_4),
% 5.24/1.00    inference(avatar_split_clause,[],[f44,f89])).
% 5.24/1.00  fof(f44,plain,(
% 5.24/1.00    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 5.24/1.00    inference(cnf_transformation,[],[f28])).
% 5.24/1.00  fof(f28,plain,(
% 5.24/1.00    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 5.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).
% 5.24/1.00  fof(f27,plain,(
% 5.24/1.00    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 5.24/1.00    introduced(choice_axiom,[])).
% 5.24/1.00  fof(f14,plain,(
% 5.24/1.00    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 5.24/1.00    inference(flattening,[],[f13])).
% 5.24/1.00  fof(f13,plain,(
% 5.24/1.00    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 5.24/1.00    inference(ennf_transformation,[],[f12])).
% 5.24/1.00  fof(f12,negated_conjecture,(
% 5.24/1.00    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 5.24/1.00    inference(negated_conjecture,[],[f11])).
% 5.24/1.00  fof(f11,conjecture,(
% 5.24/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 5.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).
% 5.24/1.00  fof(f87,plain,(
% 5.24/1.00    spl7_3),
% 5.24/1.00    inference(avatar_split_clause,[],[f43,f84])).
% 5.24/1.00  fof(f43,plain,(
% 5.24/1.00    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 5.24/1.00    inference(cnf_transformation,[],[f28])).
% 5.24/1.00  fof(f82,plain,(
% 5.24/1.00    spl7_2),
% 5.24/1.00    inference(avatar_split_clause,[],[f42,f79])).
% 5.24/1.00  fof(f42,plain,(
% 5.24/1.00    v1_funct_1(sK2)),
% 5.24/1.00    inference(cnf_transformation,[],[f28])).
% 5.24/1.00  fof(f77,plain,(
% 5.24/1.00    spl7_1),
% 5.24/1.00    inference(avatar_split_clause,[],[f41,f74])).
% 5.24/1.00  fof(f41,plain,(
% 5.24/1.00    v1_relat_1(sK2)),
% 5.24/1.00    inference(cnf_transformation,[],[f28])).
% 5.24/1.00  % SZS output end Proof for theBenchmark
% 5.24/1.00  % (20246)------------------------------
% 5.24/1.00  % (20246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.00  % (20246)Termination reason: Refutation
% 5.24/1.00  
% 5.24/1.00  % (20246)Memory used [KB]: 9722
% 5.24/1.00  % (20246)Time elapsed: 0.597 s
% 5.24/1.00  % (20246)------------------------------
% 5.24/1.00  % (20246)------------------------------
% 5.24/1.01  % (20238)Success in time 0.66 s
%------------------------------------------------------------------------------
