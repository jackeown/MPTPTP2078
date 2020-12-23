%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 169 expanded)
%              Number of leaves         :   16 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  187 ( 427 expanded)
%              Number of equality atoms :   55 ( 167 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f38,f117,f153,f109,f104,f86])).

% (7454)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f86,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ sP2(X6,X5,X8)
      | ~ sP1(X8,X5,X6)
      | X7 = X8
      | ~ sP1(X7,X5,X6)
      | ~ sP2(X6,X5,X7) ) ),
    inference(superposition,[],[f49,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X1,X0) = X2
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X0) = X2
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k7_setfam_1(X1,X0) != X2 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP1(X2,X0,X1) )
        & ( sP1(X2,X0,X1)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP2(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f104,plain,(
    sP2(k1_xboole_0,sK3,sK4) ),
    inference(resolution,[],[f102,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f102,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK3)))
      | sP2(X2,sK3,sK4) ) ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP2(X1,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP2(X1,X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f18,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X3,X0,X2] :
      ( sP0(X1,X3,X0,X2)
    <=> ( r2_hidden(X3,X2)
      <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ! [X3] :
          ( sP0(X1,X3,X0,X2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f109,plain,(
    sP1(sK4,sK3,k1_xboole_0) ),
    inference(resolution,[],[f104,f78])).

fof(f78,plain,
    ( ~ sP2(k1_xboole_0,sK3,sK4)
    | sP1(sK4,sK3,k1_xboole_0) ),
    inference(superposition,[],[f69,f75])).

fof(f75,plain,(
    sK4 = k7_setfam_1(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f74,f37])).

fof(f74,plain,
    ( sK4 = k7_setfam_1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(superposition,[],[f47,f39])).

fof(f39,plain,(
    k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1,k7_setfam_1(X1,X0))
      | sP1(k7_setfam_1(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k7_setfam_1(X1,X0) != X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f153,plain,(
    ! [X5] : sP1(k1_xboole_0,X5,k1_xboole_0) ),
    inference(resolution,[],[f146,f82])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f81,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f81,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) ),
    inference(superposition,[],[f70,f65])).

fof(f65,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f70,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X2,X2,X2))))) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f60,f63,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f146,plain,(
    ! [X15,X16] :
      ( r2_hidden(sK5(X15,X16,k1_xboole_0),X15)
      | sP1(X15,X16,k1_xboole_0) ) ),
    inference(resolution,[],[f96,f82])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,sK5(X1,X0,X2)),X2)
      | r2_hidden(sK5(X1,X0,X2),X1)
      | sP1(X1,X0,X2) ) ),
    inference(resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,sK5(X0,X1,X2),X1,X0)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ sP0(X2,sK5(X0,X1,X2),X1,X0)
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X2,X3,X1,X0)
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ~ sP0(X2,sK5(X0,X1,X2),X1,X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X3,X1,X0)
            & m1_subset_1(X3,k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ? [X3] :
            ( ~ sP0(X1,X3,X0,X2)
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( sP0(X1,X3,X0,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | r2_hidden(k3_subset_1(X2,X1),X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ~ r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | r2_hidden(X1,X3) ) ) )
      & ( ( ( r2_hidden(X1,X3)
            | ~ r2_hidden(k3_subset_1(X2,X1),X0) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X3,X0,X2] :
      ( ( sP0(X1,X3,X0,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) ) ) )
      & ( ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X3,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f117,plain,(
    ! [X0] : sP2(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f101,f40])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | sP2(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f57,f40])).

fof(f38,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:29:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (7463)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (7455)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (7463)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (7446)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (7456)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (7436)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (7448)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (7441)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (7439)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (7440)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (7456)Refutation not found, incomplete strategy% (7456)------------------------------
% 0.22/0.53  % (7456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7456)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7456)Memory used [KB]: 10746
% 0.22/0.53  % (7456)Time elapsed: 0.087 s
% 0.22/0.53  % (7456)------------------------------
% 0.22/0.53  % (7456)------------------------------
% 0.22/0.53  % (7437)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f38,f117,f153,f109,f104,f86])).
% 0.22/0.53  % (7454)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X6,X8,X7,X5] : (~sP2(X6,X5,X8) | ~sP1(X8,X5,X6) | X7 = X8 | ~sP1(X7,X5,X6) | ~sP2(X6,X5,X7)) )),
% 0.22/0.53    inference(superposition,[],[f49,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k7_setfam_1(X1,X0) = X2 | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((k7_setfam_1(X1,X0) = X2 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2)) | ~sP2(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X1,X0,X2] : (((k7_setfam_1(X0,X1) = X2 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k7_setfam_1(X0,X1) != X2)) | ~sP2(X1,X0,X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X1,X0,X2] : ((k7_setfam_1(X0,X1) = X2 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0,X2))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    sP2(k1_xboole_0,sK3,sK4)),
% 0.22/0.53    inference(resolution,[],[f102,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK3))) | sP2(X2,sK3,sK4)) )),
% 0.22/0.53    inference(resolution,[],[f57,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP2(X1,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (sP2(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(definition_folding,[],[f18,f23,f22,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X1,X3,X0,X2] : (sP0(X1,X3,X0,X2) <=> (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> ! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    sP1(sK4,sK3,k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f104,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~sP2(k1_xboole_0,sK3,sK4) | sP1(sK4,sK3,k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f69,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    sK4 = k7_setfam_1(sK3,k1_xboole_0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f74,f37])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    sK4 = k7_setfam_1(sK3,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 0.22/0.53    inference(superposition,[],[f47,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    k1_xboole_0 = k7_setfam_1(sK3,sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP2(X0,X1,k7_setfam_1(X1,X0)) | sP1(k7_setfam_1(X1,X0),X1,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2 | ~sP2(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X5] : (sP1(k1_xboole_0,X5,k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f146,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f81,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)))) )),
% 0.22/0.53    inference(superposition,[],[f70,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f43,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f44,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.53    inference(rectify,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X2,X2,X2)))))) )),
% 0.22/0.53    inference(equality_resolution,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X2,X2,X2)))))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f60,f63,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f42,f45])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f46,f62])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ( ! [X15,X16] : (r2_hidden(sK5(X15,X16,k1_xboole_0),X15) | sP1(X15,X16,k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f96,f82])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,sK5(X1,X0,X2)),X2) | r2_hidden(sK5(X1,X0,X2),X1) | sP1(X1,X0,X2)) )),
% 0.22/0.53    inference(resolution,[],[f55,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X2,sK5(X0,X1,X2),X1,X0) | sP1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~sP0(X2,sK5(X0,X1,X2),X1,X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1))) => (~sP0(X2,sK5(X0,X1,X2),X1,X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ? [X3] : (~sP0(X1,X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP1(X2,X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((~r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3)) & (r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)))) & (((r2_hidden(X1,X3) | ~r2_hidden(k3_subset_1(X2,X1),X0)) & (r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.53    inference(rectify,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X1,X3,X0,X2] : ((sP0(X1,X3,X0,X2) | ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)))) & (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~sP0(X1,X3,X0,X2)))),
% 0.22/0.53    inference(nnf_transformation,[],[f21])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0] : (sP2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f101,f40])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | sP2(X0,X1,k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f57,f40])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    k1_xboole_0 != sK4),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (7463)------------------------------
% 0.22/0.53  % (7463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7463)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (7463)Memory used [KB]: 1791
% 0.22/0.53  % (7463)Time elapsed: 0.116 s
% 0.22/0.53  % (7463)------------------------------
% 0.22/0.53  % (7463)------------------------------
% 0.22/0.53  % (7460)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (7432)Success in time 0.168 s
%------------------------------------------------------------------------------
