%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 156 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :    7
%              Number of atoms          :  260 ( 390 expanded)
%              Number of equality atoms :   61 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f49,f53,f57,f61,f65,f73,f77,f84,f94,f105,f110,f118,f125,f135,f139,f147,f156])).

fof(f156,plain,
    ( spl6_1
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl6_1
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f36,f146])).

fof(f146,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_23
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f36,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl6_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f147,plain,
    ( spl6_23
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f143,f137,f133,f123,f82,f43,f145])).

fof(f43,plain,
    ( spl6_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f82,plain,
    ( spl6_12
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f123,plain,
    ( spl6_19
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f133,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f137,plain,
    ( spl6_22
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f143,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f142,f138])).

fof(f138,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f142,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f141,f124])).

fof(f124,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f141,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f140,f83])).

fof(f83,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f140,plain,
    ( ! [X0] :
        ( k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
        | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) )
    | ~ spl6_3
    | ~ spl6_21 ),
    inference(superposition,[],[f134,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | r2_hidden(sK1(X0),X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f133])).

fof(f139,plain,
    ( spl6_22
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f121,f116,f82,f47,f43,f137])).

fof(f47,plain,
    ( spl6_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f116,plain,
    ( spl6_18
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f121,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f120,f48])).

fof(f48,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f120,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f119,f83])).

fof(f119,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(superposition,[],[f117,f44])).

fof(f117,plain,
    ( ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | r2_hidden(sK1(X0),X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f135,plain,
    ( spl6_21
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f111,f103,f55,f133])).

fof(f55,plain,
    ( spl6_6
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f103,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | r2_hidden(sK1(X0),X0) )
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(resolution,[],[f104,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | r2_hidden(sK1(X0),X0) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f125,plain,
    ( spl6_19
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f112,f108,f39,f123])).

fof(f39,plain,
    ( spl6_2
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f108,plain,
    ( spl6_17
  <=> ! [X3,X4] :
        ( k1_xboole_0 = k3_xboole_0(X3,X4)
        | ~ r1_xboole_0(X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f112,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(resolution,[],[f109,f40])).

fof(f40,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f109,plain,
    ( ! [X4,X3] :
        ( ~ r1_xboole_0(X4,X3)
        | k1_xboole_0 = k3_xboole_0(X3,X4) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f108])).

fof(f118,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f90,f75,f55,f116])).

fof(f75,plain,
    ( spl6_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f90,plain,
    ( ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | r2_hidden(sK1(X0),X0) )
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(resolution,[],[f76,f56])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f110,plain,
    ( spl6_17
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f101,f92,f59,f108])).

fof(f59,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f92,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f101,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k3_xboole_0(X3,X4)
        | ~ r1_xboole_0(X4,X3) )
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(resolution,[],[f93,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f105,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f32,f103])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f94,plain,
    ( spl6_14
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f78,f71,f63,f92])).

fof(f63,plain,
    ( spl6_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK4(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f71,plain,
    ( spl6_10
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f72,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f80,f71,f51,f39,f82])).

fof(f51,plain,
    ( spl6_5
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f80,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(superposition,[],[f72,f52])).

fof(f52,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f77,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f25,f75])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f73,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f65,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f61,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f57,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f53,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f49,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f45,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f37,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (24910)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (24911)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (24906)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (24910)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f37,f41,f45,f49,f53,f57,f61,f65,f73,f77,f84,f94,f105,f110,f118,f125,f135,f139,f147,f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    spl6_1 | ~spl6_23),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    $false | (spl6_1 | ~spl6_23)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f36,f146])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl6_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl6_23 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl6_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl6_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    spl6_23 | ~spl6_3 | ~spl6_12 | ~spl6_19 | ~spl6_21 | ~spl6_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f143,f137,f133,f123,f82,f43,f145])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl6_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl6_12 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl6_19 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl6_21 <=> ! [X1,X0] : (k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | r2_hidden(sK1(X0),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl6_22 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl6_3 | ~spl6_12 | ~spl6_19 | ~spl6_21 | ~spl6_22)),
% 0.21/0.47    inference(forward_demodulation,[],[f142,f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl6_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f137])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl6_3 | ~spl6_12 | ~spl6_19 | ~spl6_21)),
% 0.21/0.47    inference(forward_demodulation,[],[f141,f124])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl6_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f123])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | (~spl6_3 | ~spl6_12 | ~spl6_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f140,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)) ) | (~spl6_3 | ~spl6_21)),
% 0.21/0.47    inference(superposition,[],[f134,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | r2_hidden(sK1(X0),X0)) ) | ~spl6_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f133])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl6_22 | ~spl6_3 | ~spl6_4 | ~spl6_12 | ~spl6_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f121,f116,f82,f47,f43,f137])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl6_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl6_18 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | r2_hidden(sK1(X0),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_4 | ~spl6_12 | ~spl6_18)),
% 0.21/0.47    inference(forward_demodulation,[],[f120,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_12 | ~spl6_18)),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f83])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | (~spl6_3 | ~spl6_18)),
% 0.21/0.47    inference(superposition,[],[f117,f44])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | r2_hidden(sK1(X0),X0)) ) | ~spl6_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f116])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl6_21 | ~spl6_6 | ~spl6_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f111,f103,f55,f133])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl6_6 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl6_16 <=> ! [X1,X0] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | r2_hidden(sK1(X0),X0)) ) | (~spl6_6 | ~spl6_16)),
% 0.21/0.47    inference(resolution,[],[f104,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) ) | ~spl6_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) ) | ~spl6_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl6_19 | ~spl6_2 | ~spl6_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f112,f108,f39,f123])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl6_2 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl6_17 <=> ! [X3,X4] : (k1_xboole_0 = k3_xboole_0(X3,X4) | ~r1_xboole_0(X4,X3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl6_2 | ~spl6_17)),
% 0.21/0.47    inference(resolution,[],[f109,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X4,X3] : (~r1_xboole_0(X4,X3) | k1_xboole_0 = k3_xboole_0(X3,X4)) ) | ~spl6_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f108])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl6_18 | ~spl6_6 | ~spl6_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f90,f75,f55,f116])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl6_11 <=> ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | r2_hidden(sK1(X0),X0)) ) | (~spl6_6 | ~spl6_11)),
% 0.21/0.47    inference(resolution,[],[f76,f56])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl6_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f75])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl6_17 | ~spl6_7 | ~spl6_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f92,f59,f108])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl6_7 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl6_14 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X3,X4) | ~r1_xboole_0(X4,X3)) ) | (~spl6_7 | ~spl6_14)),
% 0.21/0.47    inference(resolution,[],[f93,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl6_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl6_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl6_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f103])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl6_14 | ~spl6_8 | ~spl6_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f78,f71,f63,f92])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl6_8 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl6_10 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | (~spl6_8 | ~spl6_10)),
% 0.21/0.47    inference(resolution,[],[f72,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl6_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl6_12 | ~spl6_2 | ~spl6_5 | ~spl6_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f80,f71,f51,f39,f82])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl6_5 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl6_2 | ~spl6_5 | ~spl6_10)),
% 0.21/0.47    inference(subsumption_resolution,[],[f79,f40])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl6_5 | ~spl6_10)),
% 0.21/0.47    inference(superposition,[],[f72,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl6_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl6_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f75])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl6_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f71])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl6_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl6_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f59])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl6_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f55])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl6_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f51])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl6_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f43])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl6_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f39])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~spl6_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f35])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24910)------------------------------
% 0.21/0.47  % (24910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24910)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24910)Memory used [KB]: 10618
% 0.21/0.47  % (24910)Time elapsed: 0.066 s
% 0.21/0.47  % (24910)------------------------------
% 0.21/0.47  % (24910)------------------------------
% 0.21/0.47  % (24912)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (24899)Success in time 0.11 s
%------------------------------------------------------------------------------
