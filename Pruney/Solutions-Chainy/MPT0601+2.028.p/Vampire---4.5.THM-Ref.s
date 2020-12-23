%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 164 expanded)
%              Number of leaves         :   23 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  288 ( 495 expanded)
%              Number of equality atoms :   45 (  97 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f43,f45,f49,f53,f57,f61,f68,f72,f76,f84,f110,f119,f123,f127,f131,f139,f144,f148])).

fof(f148,plain,
    ( ~ spl2_2
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f133,f83])).

fof(f83,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_11
  <=> r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f133,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f38,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f38,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f144,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5
    | spl2_11
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5
    | spl2_11
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f135,f141])).

fof(f141,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_5
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f82,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f82,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f135,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f33,f41,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k11_relat_1(X0,X1) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f41,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f139,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | spl2_15
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f117,f135])).

fof(f117,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl2_15
  <=> r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f131,plain,
    ( ~ spl2_1
    | spl2_3
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl2_1
    | spl2_3
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f118,f128])).

fof(f128,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f33,f42,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | k11_relat_1(X0,X1) = k1_xboole_0
        | ~ v1_relat_1(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k11_relat_1(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f42,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f118,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f127,plain,
    ( spl2_17
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f90,f74,f66,f125])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f74,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(superposition,[],[f75,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f123,plain,
    ( spl2_16
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f79,f70,f66,f121])).

fof(f70,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) != k1_xboole_0
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(superposition,[],[f71,f67])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X1,X0) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f119,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f91,f81,f51,f116])).

fof(f91,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f83,f52])).

fof(f110,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f64,f59,f47,f108])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f60,f48])).

fof(f48,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X0,X2) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f84,plain,
    ( spl2_11
    | spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f62,f55,f36,f81])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f62,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_2
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f37,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f37,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f76,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k9_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f72,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k9_relat_1(X1,X0) != k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f66])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,
    ( ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f44,f40,f36])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_3 ),
    inference(subsumption_resolution,[],[f22,f42])).

fof(f22,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f43,plain,
    ( spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f21,f40,f36])).

fof(f21,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f31])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (22569)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.43  % (22569)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f34,f43,f45,f49,f53,f57,f61,f68,f72,f76,f84,f110,f119,f123,f127,f131,f139,f144,f148])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    ~spl2_2 | ~spl2_11 | ~spl2_14),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f147])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    $false | (~spl2_2 | ~spl2_11 | ~spl2_14)),
% 0.20/0.43    inference(subsumption_resolution,[],[f133,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | ~spl2_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl2_11 <=> r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.43  fof(f133,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | (~spl2_2 | ~spl2_14)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f38,f109])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f108])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    spl2_14 <=> ! [X1,X0] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    spl2_2 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    ~spl2_1 | ~spl2_3 | ~spl2_5 | spl2_11 | ~spl2_16),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f143])).
% 0.20/0.43  fof(f143,plain,(
% 0.20/0.43    $false | (~spl2_1 | ~spl2_3 | ~spl2_5 | spl2_11 | ~spl2_16)),
% 0.20/0.43    inference(subsumption_resolution,[],[f135,f141])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_5 | spl2_11)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f82,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl2_5 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | spl2_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_1 | ~spl2_3 | ~spl2_16)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f33,f41,f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k11_relat_1(X0,X1) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0)) ) | ~spl2_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f121])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    spl2_16 <=> ! [X1,X0] : (k11_relat_1(X0,X1) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl2_3 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    ~spl2_1 | ~spl2_3 | spl2_15 | ~spl2_16),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    $false | (~spl2_1 | ~spl2_3 | spl2_15 | ~spl2_16)),
% 0.20/0.43    inference(subsumption_resolution,[],[f117,f135])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | spl2_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f116])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    spl2_15 <=> r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    ~spl2_1 | spl2_3 | ~spl2_15 | ~spl2_17),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f130])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    $false | (~spl2_1 | spl2_3 | ~spl2_15 | ~spl2_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f118,f128])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_1 | spl2_3 | ~spl2_17)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f33,f42,f126])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | k11_relat_1(X0,X1) = k1_xboole_0 | ~v1_relat_1(X0)) ) | ~spl2_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f125])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    spl2_17 <=> ! [X1,X0] : (k11_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f40])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~spl2_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f116])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    spl2_17 | ~spl2_8 | ~spl2_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f90,f74,f66,f125])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl2_8 <=> ! [X1,X0] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl2_10 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0)) ) | (~spl2_8 | ~spl2_10)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f85])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_8 | ~spl2_10)),
% 0.20/0.43    inference(superposition,[],[f75,f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f66])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f74])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    spl2_16 | ~spl2_8 | ~spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f70,f66,f121])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    spl2_9 <=> ! [X1,X0] : (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k11_relat_1(X0,X1) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0)) ) | (~spl2_8 | ~spl2_9)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f78])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k11_relat_1(X0,X1) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_8 | ~spl2_9)),
% 0.20/0.43    inference(superposition,[],[f71,f67])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f70])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    spl2_15 | ~spl2_5 | ~spl2_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f91,f81,f51,f116])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_5 | ~spl2_11)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f83,f52])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    spl2_14 | ~spl2_4 | ~spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f64,f59,f47,f108])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl2_4 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl2_7 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | (~spl2_4 | ~spl2_7)),
% 0.20/0.43    inference(superposition,[],[f60,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f47])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f59])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl2_11 | spl2_2 | ~spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f62,f55,f36,f81])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl2_6 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | (spl2_2 | ~spl2_6)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f37,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f55])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f36])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    spl2_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f74])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : (((k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f70])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl2_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f66])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f59])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    spl2_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f27,f55])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    spl2_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f28,f51])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    spl2_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f23,f47])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ~spl2_2 | spl2_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f44,f40,f36])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_3),
% 0.20/0.44    inference(subsumption_resolution,[],[f22,f42])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.44    inference(nnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.44    inference(negated_conjecture,[],[f7])).
% 0.20/0.44  fof(f7,conjecture,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    spl2_2 | ~spl2_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f21,f40,f36])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    spl2_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f20,f31])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    v1_relat_1(sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (22569)------------------------------
% 0.20/0.44  % (22569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (22569)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (22569)Memory used [KB]: 6140
% 0.20/0.44  % (22569)Time elapsed: 0.040 s
% 0.20/0.44  % (22569)------------------------------
% 0.20/0.44  % (22569)------------------------------
% 0.20/0.44  % (22563)Success in time 0.076 s
%------------------------------------------------------------------------------
