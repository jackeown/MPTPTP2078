%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:36 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 141 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  219 ( 511 expanded)
%              Number of equality atoms :   42 ( 100 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f126,f133])).

fof(f133,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f131,f88])).

fof(f88,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f81,f83])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k5_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f80,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

% (5847)Refutation not found, incomplete strategy% (5847)------------------------------
% (5847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5847)Termination reason: Refutation not found, incomplete strategy

% (5847)Memory used [KB]: 10618
% (5847)Time elapsed: 0.104 s
fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

% (5847)------------------------------
% (5847)------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f69,f40])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f34,f122])).

fof(f122,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f34,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f126,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f124,f34])).

fof(f124,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_1 ),
    inference(resolution,[],[f118,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f118,plain,
    ( ~ m1_subset_1(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_1
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f123,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f113,f120,f116])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK0,sK1) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ~ m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:04:41 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.35  ipcrm: permission denied for id (790003712)
% 0.14/0.35  ipcrm: permission denied for id (790265860)
% 0.14/0.36  ipcrm: permission denied for id (790298629)
% 0.14/0.36  ipcrm: permission denied for id (790429705)
% 0.14/0.37  ipcrm: permission denied for id (790560781)
% 0.14/0.37  ipcrm: permission denied for id (790659088)
% 0.14/0.37  ipcrm: permission denied for id (790691857)
% 0.14/0.37  ipcrm: permission denied for id (790724626)
% 0.14/0.37  ipcrm: permission denied for id (790757395)
% 0.14/0.37  ipcrm: permission denied for id (790790164)
% 0.14/0.38  ipcrm: permission denied for id (790036501)
% 0.14/0.38  ipcrm: permission denied for id (790822934)
% 0.14/0.38  ipcrm: permission denied for id (790888472)
% 0.14/0.38  ipcrm: permission denied for id (790921241)
% 0.14/0.38  ipcrm: permission denied for id (791019548)
% 0.14/0.39  ipcrm: permission denied for id (791085086)
% 0.19/0.40  ipcrm: permission denied for id (791314469)
% 0.19/0.40  ipcrm: permission denied for id (791380007)
% 0.19/0.41  ipcrm: permission denied for id (791609390)
% 0.19/0.41  ipcrm: permission denied for id (791642159)
% 0.19/0.41  ipcrm: permission denied for id (791707697)
% 0.19/0.42  ipcrm: permission denied for id (791838773)
% 0.19/0.42  ipcrm: permission denied for id (791871542)
% 0.19/0.42  ipcrm: permission denied for id (791904311)
% 0.19/0.42  ipcrm: permission denied for id (791937080)
% 0.19/0.42  ipcrm: permission denied for id (792002618)
% 0.19/0.42  ipcrm: permission denied for id (792068156)
% 0.19/0.43  ipcrm: permission denied for id (792100925)
% 0.19/0.43  ipcrm: permission denied for id (792264770)
% 0.19/0.43  ipcrm: permission denied for id (792297539)
% 0.19/0.43  ipcrm: permission denied for id (792330308)
% 0.19/0.43  ipcrm: permission denied for id (790102085)
% 0.19/0.44  ipcrm: permission denied for id (792395847)
% 0.19/0.44  ipcrm: permission denied for id (792461385)
% 0.19/0.44  ipcrm: permission denied for id (792526923)
% 0.19/0.44  ipcrm: permission denied for id (792592461)
% 0.19/0.45  ipcrm: permission denied for id (792625230)
% 0.19/0.45  ipcrm: permission denied for id (792723537)
% 0.19/0.45  ipcrm: permission denied for id (792756306)
% 0.19/0.45  ipcrm: permission denied for id (792821844)
% 0.19/0.45  ipcrm: permission denied for id (792854613)
% 0.19/0.46  ipcrm: permission denied for id (790134871)
% 0.19/0.46  ipcrm: permission denied for id (792985690)
% 0.19/0.46  ipcrm: permission denied for id (793083997)
% 0.19/0.47  ipcrm: permission denied for id (793149535)
% 0.19/0.47  ipcrm: permission denied for id (793215072)
% 0.19/0.47  ipcrm: permission denied for id (793247841)
% 0.19/0.47  ipcrm: permission denied for id (793280610)
% 0.19/0.48  ipcrm: permission denied for id (793444455)
% 0.19/0.48  ipcrm: permission denied for id (793608300)
% 0.19/0.49  ipcrm: permission denied for id (793772144)
% 0.19/0.49  ipcrm: permission denied for id (793903220)
% 0.19/0.49  ipcrm: permission denied for id (793968758)
% 0.19/0.49  ipcrm: permission denied for id (794001527)
% 0.19/0.50  ipcrm: permission denied for id (794034296)
% 0.19/0.50  ipcrm: permission denied for id (794132603)
% 0.19/0.50  ipcrm: permission denied for id (794198141)
% 0.36/0.64  % (5840)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.36/0.64  % (5841)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.36/0.65  % (5840)Refutation found. Thanks to Tanya!
% 0.36/0.65  % SZS status Theorem for theBenchmark
% 0.36/0.65  % (5851)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.36/0.65  % (5856)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.36/0.65  % (5837)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.36/0.66  % (5865)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.36/0.66  % (5849)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.36/0.66  % (5847)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.36/0.66  % SZS output start Proof for theBenchmark
% 0.36/0.66  fof(f134,plain,(
% 0.36/0.66    $false),
% 0.36/0.66    inference(avatar_sat_refutation,[],[f123,f126,f133])).
% 0.36/0.66  fof(f133,plain,(
% 0.36/0.66    ~spl5_2),
% 0.36/0.66    inference(avatar_contradiction_clause,[],[f132])).
% 0.36/0.66  fof(f132,plain,(
% 0.36/0.66    $false | ~spl5_2),
% 0.36/0.66    inference(subsumption_resolution,[],[f131,f88])).
% 0.36/0.66  fof(f88,plain,(
% 0.36/0.66    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.36/0.66    inference(backward_demodulation,[],[f81,f83])).
% 0.36/0.66  fof(f83,plain,(
% 0.36/0.66    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.36/0.66    inference(resolution,[],[f81,f39])).
% 0.36/0.66  fof(f39,plain,(
% 0.36/0.66    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.36/0.66    inference(cnf_transformation,[],[f27])).
% 0.36/0.66  fof(f27,plain,(
% 0.36/0.66    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.36/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f26])).
% 0.36/0.66  fof(f26,plain,(
% 0.36/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.36/0.66    introduced(choice_axiom,[])).
% 0.36/0.66  fof(f16,plain,(
% 0.36/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.36/0.66    inference(ennf_transformation,[],[f4])).
% 0.36/0.66  fof(f4,axiom,(
% 0.36/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.36/0.66  fof(f81,plain,(
% 0.36/0.66    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0))) )),
% 0.36/0.66    inference(subsumption_resolution,[],[f80,f75])).
% 0.36/0.66  fof(f75,plain,(
% 0.36/0.66    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,X0)) )),
% 0.36/0.66    inference(superposition,[],[f68,f40])).
% 0.36/0.66  fof(f40,plain,(
% 0.36/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.36/0.66    inference(cnf_transformation,[],[f14])).
% 0.36/0.66  fof(f14,plain,(
% 0.36/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.36/0.66    inference(rectify,[],[f3])).
% 0.36/0.66  fof(f3,axiom,(
% 0.36/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.36/0.66  fof(f68,plain,(
% 0.36/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.36/0.66    inference(equality_resolution,[],[f65])).
% 0.36/0.66  fof(f65,plain,(
% 0.36/0.66    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.36/0.66    inference(definition_unfolding,[],[f50,f42])).
% 0.36/0.66  fof(f42,plain,(
% 0.36/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.36/0.66    inference(cnf_transformation,[],[f5])).
% 0.36/0.66  fof(f5,axiom,(
% 0.36/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.36/0.66  fof(f50,plain,(
% 0.36/0.66    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.36/0.66    inference(cnf_transformation,[],[f33])).
% 0.36/0.66  fof(f33,plain,(
% 0.36/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.36/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.36/0.66  fof(f32,plain,(
% 0.36/0.66    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.36/0.66    introduced(choice_axiom,[])).
% 0.36/0.66  fof(f31,plain,(
% 0.36/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.36/0.66    inference(rectify,[],[f30])).
% 0.36/0.66  fof(f30,plain,(
% 0.36/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.36/0.66    inference(flattening,[],[f29])).
% 0.36/0.66  % (5847)Refutation not found, incomplete strategy% (5847)------------------------------
% 0.36/0.66  % (5847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.66  % (5847)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.66  
% 0.36/0.66  % (5847)Memory used [KB]: 10618
% 0.36/0.66  % (5847)Time elapsed: 0.104 s
% 0.36/0.66  fof(f29,plain,(
% 0.36/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.36/0.66    inference(nnf_transformation,[],[f2])).
% 0.36/0.66  % (5847)------------------------------
% 0.36/0.66  % (5847)------------------------------
% 0.36/0.66  fof(f2,axiom,(
% 0.36/0.66    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.36/0.66  fof(f80,plain,(
% 0.36/0.66    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 0.36/0.66    inference(superposition,[],[f69,f40])).
% 0.36/0.66  fof(f69,plain,(
% 0.36/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 0.36/0.66    inference(equality_resolution,[],[f66])).
% 0.36/0.66  fof(f66,plain,(
% 0.36/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.36/0.66    inference(definition_unfolding,[],[f49,f42])).
% 0.36/0.66  fof(f49,plain,(
% 0.36/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.36/0.66    inference(cnf_transformation,[],[f33])).
% 0.36/0.66  fof(f131,plain,(
% 0.36/0.66    r2_hidden(sK0,k1_xboole_0) | ~spl5_2),
% 0.36/0.66    inference(backward_demodulation,[],[f34,f122])).
% 0.36/0.66  fof(f122,plain,(
% 0.36/0.66    k1_xboole_0 = sK1 | ~spl5_2),
% 0.36/0.66    inference(avatar_component_clause,[],[f120])).
% 0.36/0.66  fof(f120,plain,(
% 0.36/0.66    spl5_2 <=> k1_xboole_0 = sK1),
% 0.36/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.36/0.66  fof(f34,plain,(
% 0.36/0.66    r2_hidden(sK0,sK1)),
% 0.36/0.66    inference(cnf_transformation,[],[f21])).
% 0.36/0.66  fof(f21,plain,(
% 0.36/0.66    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1)),
% 0.36/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).
% 0.36/0.66  fof(f20,plain,(
% 0.36/0.66    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1))),
% 0.36/0.66    introduced(choice_axiom,[])).
% 0.36/0.66  fof(f15,plain,(
% 0.36/0.66    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.36/0.66    inference(ennf_transformation,[],[f13])).
% 0.36/0.66  fof(f13,negated_conjecture,(
% 0.36/0.66    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.36/0.66    inference(negated_conjecture,[],[f12])).
% 0.36/0.66  fof(f12,conjecture,(
% 0.36/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.36/0.66  fof(f126,plain,(
% 0.36/0.66    spl5_1),
% 0.36/0.66    inference(avatar_contradiction_clause,[],[f125])).
% 0.36/0.66  fof(f125,plain,(
% 0.36/0.66    $false | spl5_1),
% 0.36/0.66    inference(subsumption_resolution,[],[f124,f34])).
% 0.36/0.66  fof(f124,plain,(
% 0.36/0.66    ~r2_hidden(sK0,sK1) | spl5_1),
% 0.36/0.66    inference(resolution,[],[f118,f70])).
% 0.36/0.66  fof(f70,plain,(
% 0.36/0.66    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.36/0.66    inference(subsumption_resolution,[],[f44,f37])).
% 0.36/0.66  fof(f37,plain,(
% 0.36/0.66    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.36/0.66    inference(cnf_transformation,[],[f25])).
% 0.36/0.66  fof(f25,plain,(
% 0.36/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.36/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 0.36/0.66  fof(f24,plain,(
% 0.36/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.36/0.66    introduced(choice_axiom,[])).
% 0.36/0.66  fof(f23,plain,(
% 0.36/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.36/0.66    inference(rectify,[],[f22])).
% 0.36/0.66  fof(f22,plain,(
% 0.36/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.36/0.66    inference(nnf_transformation,[],[f1])).
% 0.36/0.66  fof(f1,axiom,(
% 0.36/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.36/0.66  fof(f44,plain,(
% 0.36/0.66    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.36/0.66    inference(cnf_transformation,[],[f28])).
% 0.36/0.66  fof(f28,plain,(
% 0.36/0.66    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.36/0.66    inference(nnf_transformation,[],[f17])).
% 0.36/0.66  fof(f17,plain,(
% 0.36/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.36/0.66    inference(ennf_transformation,[],[f10])).
% 0.36/0.66  fof(f10,axiom,(
% 0.36/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.36/0.66  fof(f118,plain,(
% 0.36/0.66    ~m1_subset_1(sK0,sK1) | spl5_1),
% 0.36/0.66    inference(avatar_component_clause,[],[f116])).
% 0.36/0.66  fof(f116,plain,(
% 0.36/0.66    spl5_1 <=> m1_subset_1(sK0,sK1)),
% 0.36/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.36/0.66  fof(f123,plain,(
% 0.36/0.66    ~spl5_1 | spl5_2),
% 0.36/0.66    inference(avatar_split_clause,[],[f113,f120,f116])).
% 0.36/0.66  fof(f113,plain,(
% 0.36/0.66    k1_xboole_0 = sK1 | ~m1_subset_1(sK0,sK1)),
% 0.36/0.66    inference(resolution,[],[f60,f59])).
% 0.36/0.66  fof(f59,plain,(
% 0.36/0.66    ~m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))),
% 0.36/0.66    inference(definition_unfolding,[],[f35,f58])).
% 0.36/0.66  fof(f58,plain,(
% 0.36/0.66    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.36/0.66    inference(definition_unfolding,[],[f36,f57])).
% 0.36/0.66  fof(f57,plain,(
% 0.36/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.36/0.66    inference(definition_unfolding,[],[f41,f56])).
% 0.36/0.66  fof(f56,plain,(
% 0.36/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.36/0.66    inference(definition_unfolding,[],[f48,f55])).
% 0.36/0.66  fof(f55,plain,(
% 0.36/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.36/0.66    inference(cnf_transformation,[],[f9])).
% 0.36/0.66  fof(f9,axiom,(
% 0.36/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.36/0.66  fof(f48,plain,(
% 0.36/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.36/0.66    inference(cnf_transformation,[],[f8])).
% 0.36/0.66  fof(f8,axiom,(
% 0.36/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.36/0.66  fof(f41,plain,(
% 0.36/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.36/0.66    inference(cnf_transformation,[],[f7])).
% 0.36/0.66  fof(f7,axiom,(
% 0.36/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.36/0.66  fof(f36,plain,(
% 0.36/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.36/0.66    inference(cnf_transformation,[],[f6])).
% 0.36/0.66  fof(f6,axiom,(
% 0.36/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.36/0.66  fof(f35,plain,(
% 0.36/0.66    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.36/0.66    inference(cnf_transformation,[],[f21])).
% 0.36/0.66  fof(f60,plain,(
% 0.36/0.66    ( ! [X0,X1] : (m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.36/0.66    inference(definition_unfolding,[],[f47,f58])).
% 0.36/0.66  fof(f47,plain,(
% 0.36/0.66    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.36/0.66    inference(cnf_transformation,[],[f19])).
% 0.36/0.66  fof(f19,plain,(
% 0.36/0.66    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.36/0.66    inference(flattening,[],[f18])).
% 0.36/0.66  fof(f18,plain,(
% 0.36/0.66    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.36/0.66    inference(ennf_transformation,[],[f11])).
% 0.36/0.66  fof(f11,axiom,(
% 0.36/0.66    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.36/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.36/0.66  % SZS output end Proof for theBenchmark
% 0.36/0.66  % (5840)------------------------------
% 0.36/0.66  % (5840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.66  % (5840)Termination reason: Refutation
% 0.36/0.66  
% 0.36/0.66  % (5840)Memory used [KB]: 10746
% 0.36/0.66  % (5840)Time elapsed: 0.103 s
% 0.36/0.66  % (5840)------------------------------
% 0.36/0.66  % (5840)------------------------------
% 0.36/0.66  % (5643)Success in time 0.317 s
%------------------------------------------------------------------------------
