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
% DateTime   : Thu Dec  3 12:50:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 177 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  336 ( 616 expanded)
%              Number of equality atoms :   45 ( 104 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f79,f311,f345,f377,f1207,f1284,f1317,f1319])).

fof(f1319,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1318])).

fof(f1318,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f314,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f314,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_6 ),
    inference(trivial_inequality_removal,[],[f313])).

fof(f313,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK1)
    | spl5_6 ),
    inference(superposition,[],[f308,f119])).

fof(f119,plain,(
    ! [X2] :
      ( k1_xboole_0 = k10_relat_1(X2,k1_xboole_0)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f111,f87])).

fof(f87,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f55,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f68,f47])).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k10_relat_1(X0,k1_xboole_0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f109,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f109,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f66,f80])).

fof(f80,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f308,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl5_6
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1317,plain,
    ( ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1308,f71,f306,f302,f75])).

fof(f75,plain,
    ( spl5_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f302,plain,
    ( spl5_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f71,plain,
    ( spl5_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1308,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl5_1 ),
    inference(superposition,[],[f73,f167])).

fof(f167,plain,(
    ! [X2,X3] :
      ( k10_relat_1(X2,k1_xboole_0) = k10_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k2_relat_1(X2),X3) ) ),
    inference(forward_demodulation,[],[f165,f82])).

fof(f165,plain,(
    ! [X2,X3] :
      ( k10_relat_1(X2,X3) = k10_relat_1(X2,k4_xboole_0(k2_relat_1(X2),k2_relat_1(X2)))
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k2_relat_1(X2),X3) ) ),
    inference(superposition,[],[f69,f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f73,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f1284,plain,
    ( spl5_2
    | ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f1282])).

fof(f1282,plain,
    ( $false
    | spl5_2
    | ~ spl5_30 ),
    inference(resolution,[],[f1281,f77])).

fof(f77,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f1281,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl5_30 ),
    inference(duplicate_literal_removal,[],[f1279])).

fof(f1279,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl5_30 ),
    inference(resolution,[],[f1228,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1228,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2(k2_relat_1(sK1),X4),sK0)
        | r1_xboole_0(k2_relat_1(sK1),X4) )
    | ~ spl5_30 ),
    inference(resolution,[],[f1206,f50])).

fof(f1206,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1205,plain,
    ( spl5_30
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1207,plain,
    ( ~ spl5_5
    | spl5_30
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f1198,f375,f1205,f302])).

fof(f375,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(sK3(X0,X1,sK1),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f1194])).

fof(f1194,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_12 ),
    inference(superposition,[],[f1164,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f1164,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k9_relat_1(sK1,X5))
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X4,k2_relat_1(sK1)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f376,f80])).

fof(f376,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,sK1),k1_xboole_0)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f375])).

fof(f377,plain,
    ( ~ spl5_5
    | spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f372,f343,f375,f302])).

fof(f343,plain,
    ( spl5_10
  <=> ! [X1,X2] :
        ( r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X1,X2),sK1)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f372,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(sK3(X0,X1,sK1),k1_xboole_0)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_10 ),
    inference(resolution,[],[f344,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f344,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),sK1)
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f343])).

fof(f345,plain,
    ( ~ spl5_5
    | spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f341,f71,f343,f302])).

fof(f341,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(k4_tarski(X1,X2),sK1)
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_1 ),
    inference(superposition,[],[f67,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f311,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f304,f42])).

fof(f304,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f302])).

fof(f79,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f43,f75,f71])).

fof(f43,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f44,f75,f71])).

fof(f44,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (20194)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (20186)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (20185)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (20182)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (20195)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (20187)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (20189)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (20188)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (20193)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (20190)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (20192)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (20192)Refutation not found, incomplete strategy% (20192)------------------------------
% 0.21/0.50  % (20192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20192)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20192)Memory used [KB]: 10618
% 0.21/0.50  % (20192)Time elapsed: 0.076 s
% 0.21/0.50  % (20192)------------------------------
% 0.21/0.50  % (20192)------------------------------
% 0.21/0.50  % (20181)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (20198)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (20183)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (20185)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1320,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f78,f79,f311,f345,f377,f1207,f1284,f1317,f1319])).
% 0.21/0.51  fof(f1319,plain,(
% 0.21/0.51    spl5_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1318])).
% 0.21/0.51  fof(f1318,plain,(
% 0.21/0.51    $false | spl5_6),
% 0.21/0.51    inference(resolution,[],[f314,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | spl5_6),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f313])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK1) | spl5_6),
% 0.21/0.51    inference(superposition,[],[f308,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X2] : (k1_xboole_0 = k10_relat_1(X2,k1_xboole_0) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(resolution,[],[f111,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_xboole_0(X1,X1) | k1_xboole_0 = X1) )),
% 0.21/0.51    inference(superposition,[],[f55,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f68,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f46,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(k10_relat_1(X0,k1_xboole_0),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f109,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) | ~v1_relat_1(X5)) )),
% 0.21/0.51    inference(resolution,[],[f66,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f57,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(rectify,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | spl5_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f306])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    spl5_6 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f1317,plain,(
% 0.21/0.51    ~spl5_2 | ~spl5_5 | ~spl5_6 | spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f1308,f71,f306,f302,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl5_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    spl5_5 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl5_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f1308,plain,(
% 0.21/0.51    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | ~v1_relat_1(sK1) | ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl5_1),
% 0.21/0.51    inference(superposition,[],[f73,f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k10_relat_1(X2,k1_xboole_0) = k10_relat_1(X2,X3) | ~v1_relat_1(X2) | ~r1_xboole_0(k2_relat_1(X2),X3)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f165,f82])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k10_relat_1(X2,X3) = k10_relat_1(X2,k4_xboole_0(k2_relat_1(X2),k2_relat_1(X2))) | ~v1_relat_1(X2) | ~r1_xboole_0(k2_relat_1(X2),X3)) )),
% 0.21/0.51    inference(superposition,[],[f69,f55])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f53,f49])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f1284,plain,(
% 0.21/0.51    spl5_2 | ~spl5_30),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1282])).
% 0.21/0.51  fof(f1282,plain,(
% 0.21/0.51    $false | (spl5_2 | ~spl5_30)),
% 0.21/0.51    inference(resolution,[],[f1281,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f1281,plain,(
% 0.21/0.51    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl5_30),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f1279])).
% 0.21/0.51  fof(f1279,plain,(
% 0.21/0.51    r1_xboole_0(k2_relat_1(sK1),sK0) | r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl5_30),
% 0.21/0.51    inference(resolution,[],[f1228,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f1228,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(sK2(k2_relat_1(sK1),X4),sK0) | r1_xboole_0(k2_relat_1(sK1),X4)) ) | ~spl5_30),
% 0.21/0.51    inference(resolution,[],[f1206,f50])).
% 0.21/0.51  fof(f1206,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f1205])).
% 0.21/0.51  fof(f1205,plain,(
% 0.21/0.51    spl5_30 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.51  fof(f1207,plain,(
% 0.21/0.51    ~spl5_5 | spl5_30 | ~spl5_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f1198,f375,f1205,f302])).
% 0.21/0.51  fof(f375,plain,(
% 0.21/0.51    spl5_12 <=> ! [X1,X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(X0,sK0) | r2_hidden(sK3(X0,X1,sK1),k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.51  fof(f1198,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK1)) ) | ~spl5_12),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f1194])).
% 0.21/0.51  fof(f1194,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl5_12),
% 0.21/0.51    inference(superposition,[],[f1164,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.51  fof(f1164,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_hidden(X4,k9_relat_1(sK1,X5)) | ~r2_hidden(X4,sK0) | ~r2_hidden(X4,k2_relat_1(sK1))) ) | ~spl5_12),
% 0.21/0.51    inference(resolution,[],[f376,f80])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),k1_xboole_0) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl5_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f375])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    ~spl5_5 | spl5_12 | ~spl5_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f372,f343,f375,f302])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    spl5_10 <=> ! [X1,X2] : (r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X2,k2_relat_1(sK1)) | ~r2_hidden(k4_tarski(X1,X2),sK1) | ~r2_hidden(X2,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(sK3(X0,X1,sK1),k1_xboole_0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | ~spl5_10),
% 0.21/0.51    inference(resolution,[],[f344,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(rectify,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK1) | ~r2_hidden(X2,k2_relat_1(sK1)) | r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X2,sK0)) ) | ~spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f343])).
% 0.21/0.51  fof(f345,plain,(
% 0.21/0.51    ~spl5_5 | spl5_10 | ~spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f341,f71,f343,f302])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X2,sK0) | ~r2_hidden(k4_tarski(X1,X2),sK1) | ~r2_hidden(X2,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl5_1),
% 0.21/0.51    inference(superposition,[],[f67,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    spl5_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f310])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    $false | spl5_5),
% 0.21/0.51    inference(resolution,[],[f304,f42])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | spl5_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f302])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl5_1 | spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f75,f71])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f75,f71])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (20185)------------------------------
% 0.21/0.51  % (20185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20185)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (20185)Memory used [KB]: 6652
% 0.21/0.51  % (20185)Time elapsed: 0.079 s
% 0.21/0.51  % (20185)------------------------------
% 0.21/0.51  % (20185)------------------------------
% 0.21/0.51  % (20180)Success in time 0.146 s
%------------------------------------------------------------------------------
