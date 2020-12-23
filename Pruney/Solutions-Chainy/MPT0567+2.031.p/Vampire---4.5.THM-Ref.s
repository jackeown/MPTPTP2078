%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 134 expanded)
%              Number of leaves         :   30 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :  270 ( 358 expanded)
%              Number of equality atoms :   44 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f65,f69,f73,f77,f81,f85,f93,f110,f144,f183,f203,f222,f224,f227])).

fof(f227,plain,
    ( ~ spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(resolution,[],[f105,f50])).

fof(f50,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f105,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_15
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f224,plain,
    ( ~ spl4_16
    | spl4_19
    | spl4_20
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f223,f79,f58,f53,f129,f126,f107])).

fof(f107,plain,
    ( spl4_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f126,plain,
    ( spl4_19
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f129,plain,
    ( spl4_20
  <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f53,plain,
    ( spl4_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f58,plain,
    ( spl4_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f79,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X1),k1_relat_1(X1))
        | ~ r2_hidden(X0,k2_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f223,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f118,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f80,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(X1))
        | r2_hidden(sK2(X1),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f222,plain,
    ( ~ spl4_7
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f220,f72])).

fof(f72,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_7
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f220,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK2(k1_xboole_0)),k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(resolution,[],[f131,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k2_xboole_0(k1_tarski(X0),X1) = X1 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(k1_tarski(X0),X1) = X1
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f131,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f129])).

fof(f203,plain,
    ( spl4_1
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl4_1
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f193,f45])).

fof(f45,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f193,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(resolution,[],[f182,f127])).

fof(f127,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f126])).

fof(f182,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_29
  <=> ! [X0] :
        ( r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f183,plain,
    ( spl4_29
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f177,f142,f48,f181])).

fof(f142,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK1(k10_relat_1(X0,X1)),X1,X0),X1)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k10_relat_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f177,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) )
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(resolution,[],[f143,f50])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK1(k10_relat_1(X0,X1)),X1,X0),X1)
        | k1_xboole_0 = k10_relat_1(X0,X1) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( spl4_22
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f140,f91,f67,f142])).

fof(f67,plain,
    ( spl4_6
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f91,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK3(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1(k10_relat_1(X0,X1)),X1,X0),X1)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k10_relat_1(X0,X1) )
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f92,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | r2_hidden(sK3(X0,X1,X2),X1)
        | ~ v1_relat_1(X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f110,plain,
    ( spl4_15
    | spl4_16
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f102,f75,f63,f107,f104])).

fof(f63,plain,
    ( spl4_5
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f75,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f102,plain,
    ( ! [X0] :
        ( v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(superposition,[],[f76,f64])).

fof(f64,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f93,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f85,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f81,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

fof(f22,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK2(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f77,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f73,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f69,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f65,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f61,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f58])).

fof(f30,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f56,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f46,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f43])).

fof(f29,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:07:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (28399)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (28395)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.42  % (28399)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f228,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f65,f69,f73,f77,f81,f85,f93,f110,f144,f183,f203,f222,f224,f227])).
% 0.22/0.42  fof(f227,plain,(
% 0.22/0.42    ~spl4_2 | ~spl4_15),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f225])).
% 0.22/0.42  fof(f225,plain,(
% 0.22/0.42    $false | (~spl4_2 | ~spl4_15)),
% 0.22/0.42    inference(resolution,[],[f105,f50])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    v1_relat_1(sK0) | ~spl4_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f48])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl4_2 <=> v1_relat_1(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.42  fof(f105,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl4_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f104])).
% 0.22/0.42  fof(f104,plain,(
% 0.22/0.42    spl4_15 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.42  fof(f224,plain,(
% 0.22/0.42    ~spl4_16 | spl4_19 | spl4_20 | ~spl4_3 | ~spl4_4 | ~spl4_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f223,f79,f58,f53,f129,f126,f107])).
% 0.22/0.42  fof(f107,plain,(
% 0.22/0.42    spl4_16 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.42  fof(f126,plain,(
% 0.22/0.42    spl4_19 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.42  fof(f129,plain,(
% 0.22/0.42    spl4_20 <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl4_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    spl4_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.42  fof(f79,plain,(
% 0.22/0.42    spl4_9 <=> ! [X1,X0] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.43  fof(f223,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_9)),
% 0.22/0.43    inference(forward_demodulation,[],[f118,f60])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f58])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_3 | ~spl4_9)),
% 0.22/0.43    inference(superposition,[],[f80,f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK2(X1),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f79])).
% 0.22/0.43  fof(f222,plain,(
% 0.22/0.43    ~spl4_7 | ~spl4_10 | ~spl4_20),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f221])).
% 0.22/0.43  fof(f221,plain,(
% 0.22/0.43    $false | (~spl4_7 | ~spl4_10 | ~spl4_20)),
% 0.22/0.43    inference(subsumption_resolution,[],[f220,f72])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl4_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f71])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    spl4_7 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.43  fof(f220,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2(k1_xboole_0)),k1_xboole_0) | (~spl4_10 | ~spl4_20)),
% 0.22/0.43    inference(resolution,[],[f131,f84])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) ) | ~spl4_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f83])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    spl4_10 <=> ! [X1,X0] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.43  fof(f131,plain,(
% 0.22/0.43    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~spl4_20),
% 0.22/0.43    inference(avatar_component_clause,[],[f129])).
% 0.22/0.43  fof(f203,plain,(
% 0.22/0.43    spl4_1 | ~spl4_19 | ~spl4_29),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f202])).
% 0.22/0.43  fof(f202,plain,(
% 0.22/0.43    $false | (spl4_1 | ~spl4_19 | ~spl4_29)),
% 0.22/0.43    inference(subsumption_resolution,[],[f193,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f43])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl4_1 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f193,plain,(
% 0.22/0.43    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | (~spl4_19 | ~spl4_29)),
% 0.22/0.43    inference(resolution,[],[f182,f127])).
% 0.22/0.43  fof(f127,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_19),
% 0.22/0.43    inference(avatar_component_clause,[],[f126])).
% 0.22/0.43  fof(f182,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0)) ) | ~spl4_29),
% 0.22/0.43    inference(avatar_component_clause,[],[f181])).
% 0.22/0.43  fof(f181,plain,(
% 0.22/0.43    spl4_29 <=> ! [X0] : (r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.43  fof(f183,plain,(
% 0.22/0.43    spl4_29 | ~spl4_2 | ~spl4_22),
% 0.22/0.43    inference(avatar_split_clause,[],[f177,f142,f48,f181])).
% 0.22/0.43  fof(f142,plain,(
% 0.22/0.43    spl4_22 <=> ! [X1,X0] : (r2_hidden(sK3(sK1(k10_relat_1(X0,X1)),X1,X0),X1) | ~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.43  fof(f177,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0)) ) | (~spl4_2 | ~spl4_22)),
% 0.22/0.43    inference(resolution,[],[f143,f50])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(sK1(k10_relat_1(X0,X1)),X1,X0),X1) | k1_xboole_0 = k10_relat_1(X0,X1)) ) | ~spl4_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f142])).
% 0.22/0.43  fof(f144,plain,(
% 0.22/0.43    spl4_22 | ~spl4_6 | ~spl4_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f140,f91,f67,f142])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl4_6 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    spl4_12 <=> ! [X1,X0,X2] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.43  fof(f140,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK3(sK1(k10_relat_1(X0,X1)),X1,X0),X1) | ~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,X1)) ) | (~spl4_6 | ~spl4_12)),
% 0.22/0.43    inference(resolution,[],[f92,f68])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f67])).
% 0.22/0.43  fof(f92,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1) | ~v1_relat_1(X2)) ) | ~spl4_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f91])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    spl4_15 | spl4_16 | ~spl4_5 | ~spl4_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f102,f75,f63,f107,f104])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl4_5 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    spl4_8 <=> ! [X1,X0] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) ) | (~spl4_5 | ~spl4_8)),
% 0.22/0.43    inference(superposition,[],[f76,f64])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl4_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl4_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f75])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    spl4_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f40,f91])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(rectify,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(nnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    spl4_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f37,f83])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    spl4_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f36,f79])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK2(X1),k1_relat_1(X1)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl4_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f35,f75])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    spl4_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f34,f71])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl4_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f33,f67])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl4_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f32,f63])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl4_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f30,f58])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl4_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f31,f53])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl4_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f28,f48])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.22/0.43    inference(negated_conjecture,[],[f9])).
% 0.22/0.43  fof(f9,conjecture,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ~spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f29,f43])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (28399)------------------------------
% 0.22/0.43  % (28399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (28399)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (28399)Memory used [KB]: 10618
% 0.22/0.43  % (28399)Time elapsed: 0.009 s
% 0.22/0.43  % (28399)------------------------------
% 0.22/0.43  % (28399)------------------------------
% 0.22/0.43  % (28393)Success in time 0.067 s
%------------------------------------------------------------------------------
