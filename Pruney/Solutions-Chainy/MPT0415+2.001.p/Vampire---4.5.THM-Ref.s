%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:21 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 437 expanded)
%              Number of leaves         :   17 ( 121 expanded)
%              Depth                    :   18
%              Number of atoms          :  244 (1283 expanded)
%              Number of equality atoms :   73 ( 481 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2065,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2064,f1471])).

fof(f1471,plain,(
    ! [X0] : ~ r2_hidden(k4_xboole_0(sK2,X0),sK3) ),
    inference(subsumption_resolution,[],[f1468,f83])).

fof(f83,plain,(
    ! [X2,X3] : m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X2)) ),
    inference(superposition,[],[f68,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f44,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f1468,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_xboole_0(sK2,X0),sK3)
      | ~ m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(sK2)) ) ),
    inference(superposition,[],[f1467,f340])).

fof(f340,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k3_subset_1(X4,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f335,f115])).

fof(f115,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f81,f107])).

fof(f107,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f76,f79])).

fof(f79,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f73,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f47,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f49,f72])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f60,f68])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f48,f48])).

fof(f335,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k3_subset_1(X4,k3_xboole_0(X4,X5)) ),
    inference(resolution,[],[f50,f83])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1467,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_subset_1(sK2,X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1465,f69])).

fof(f69,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f43,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f1465,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_subset_1(sK2,X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f55,f1205])).

fof(f1205,plain,(
    sP0(sK3,sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f708,f1201])).

fof(f1201,plain,(
    sP1(k1_xboole_0,sK2,sK3) ),
    inference(resolution,[],[f1196,f648])).

fof(f648,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(subsumption_resolution,[],[f647,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f647,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(superposition,[],[f51,f42])).

fof(f42,plain,(
    k1_xboole_0 = k7_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f1196,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | sP1(X13,sK2,sK3) ) ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP1(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X2,X0,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f22,f27,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> r2_hidden(k3_subset_1(X0,X3),X1) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f708,plain,
    ( ~ sP1(k1_xboole_0,sK2,sK3)
    | sP0(sK3,sK2,k1_xboole_0) ),
    inference(superposition,[],[f65,f42])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ sP1(k7_setfam_1(X1,X2),X1,X2)
      | sP0(X2,X1,k7_setfam_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k7_setfam_1(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k7_setfam_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k3_subset_1(X1,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) )
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X2)
                | ~ r2_hidden(k3_subset_1(X1,X4),X0) )
              & ( r2_hidden(k3_subset_1(X1,X4),X0)
                | ~ r2_hidden(X4,X2) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X1,X3),X0)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X1,X3),X0)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ( ~ r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k3_subset_1(X1,X3),X0)
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(k3_subset_1(X1,X3),X0)
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X2)
                | ~ r2_hidden(k3_subset_1(X1,X4),X0) )
              & ( r2_hidden(k3_subset_1(X1,X4),X0)
                | ~ r2_hidden(X4,X2) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(k3_subset_1(X0,X3),X1)
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
              & ( r2_hidden(k3_subset_1(X0,X3),X1)
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(k3_subset_1(X0,X3),X1)
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
              & ( r2_hidden(k3_subset_1(X0,X3),X1)
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f2064,plain,(
    r2_hidden(k4_xboole_0(sK2,sK4(sK3,sK2,sK3)),sK3) ),
    inference(forward_demodulation,[],[f2063,f2038])).

fof(f2038,plain,(
    k4_xboole_0(sK2,sK4(sK3,sK2,sK3)) = k3_subset_1(sK2,sK4(sK3,sK2,sK3)) ),
    inference(superposition,[],[f340,f2007])).

fof(f2007,plain,(
    sK4(sK3,sK2,sK3) = k3_xboole_0(sK2,sK4(sK3,sK2,sK3)) ),
    inference(resolution,[],[f430,f1209])).

fof(f1209,plain,(
    ~ sP0(sK3,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1208,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f1208,plain,
    ( k1_xboole_0 = sK3
    | ~ sP0(sK3,sK2,sK3) ),
    inference(forward_demodulation,[],[f1207,f42])).

fof(f1207,plain,
    ( ~ sP0(sK3,sK2,sK3)
    | sK3 = k7_setfam_1(sK2,sK3) ),
    inference(resolution,[],[f1203,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k7_setfam_1(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1203,plain,(
    sP1(sK3,sK2,sK3) ),
    inference(resolution,[],[f1196,f40])).

fof(f430,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK4(X0,X1,X2) = k3_xboole_0(X1,sK4(X0,X1,X2)) ) ),
    inference(forward_demodulation,[],[f429,f79])).

fof(f429,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK4(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f428,f49])).

fof(f428,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(sK4(X3,X4,X5),X4)
      | sP0(X3,X4,X5) ) ),
    inference(resolution,[],[f56,f60])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2063,plain,(
    r2_hidden(k3_subset_1(sK2,sK4(sK3,sK2,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f2061,f1209])).

fof(f2061,plain,
    ( r2_hidden(k3_subset_1(sK2,sK4(sK3,sK2,sK3)),sK3)
    | sP0(sK3,sK2,sK3) ),
    inference(resolution,[],[f2013,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2013,plain,(
    ~ r2_hidden(sK4(sK3,sK2,sK3),sK3) ),
    inference(superposition,[],[f1472,f2007])).

fof(f1472,plain,(
    ! [X2] : ~ r2_hidden(k3_xboole_0(sK2,X2),sK3) ),
    inference(subsumption_resolution,[],[f1470,f68])).

fof(f1470,plain,(
    ! [X2] :
      ( ~ r2_hidden(k3_xboole_0(sK2,X2),sK3)
      | ~ m1_subset_1(k4_xboole_0(sK2,X2),k1_zfmisc_1(sK2)) ) ),
    inference(superposition,[],[f1467,f338])).

fof(f338,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f333,f48])).

fof(f333,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f50,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (26822)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (26806)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (26801)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (26817)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (26809)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (26811)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (26814)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (26811)Refutation not found, incomplete strategy% (26811)------------------------------
% 0.21/0.54  % (26811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26803)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (26811)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26811)Memory used [KB]: 6140
% 0.21/0.54  % (26811)Time elapsed: 0.004 s
% 0.21/0.54  % (26811)------------------------------
% 0.21/0.54  % (26811)------------------------------
% 0.21/0.55  % (26796)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.54/0.56  % (26799)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.54/0.56  % (26815)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.57  % (26823)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.54/0.57  % (26807)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.57  % (26816)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.57  % (26808)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.57  % (26800)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.64/0.58  % (26798)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.58  % (26819)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.64/0.59  % (26813)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.64/0.59  % (26813)Refutation not found, incomplete strategy% (26813)------------------------------
% 1.64/0.59  % (26813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (26813)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (26813)Memory used [KB]: 10618
% 1.64/0.59  % (26813)Time elapsed: 0.168 s
% 1.64/0.59  % (26813)------------------------------
% 1.64/0.59  % (26813)------------------------------
% 1.64/0.59  % (26816)Refutation not found, incomplete strategy% (26816)------------------------------
% 1.64/0.59  % (26816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (26821)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.64/0.59  % (26802)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.59  % (26816)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (26816)Memory used [KB]: 10746
% 1.64/0.59  % (26816)Time elapsed: 0.164 s
% 1.64/0.59  % (26816)------------------------------
% 1.64/0.59  % (26816)------------------------------
% 1.64/0.60  % (26805)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.64/0.60  % (26797)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.64/0.60  % (26824)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.64/0.61  % (26810)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.64/0.61  % (26826)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.62  % (26812)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.64/0.63  % (26818)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.64/0.63  % (26803)Refutation found. Thanks to Tanya!
% 1.64/0.63  % SZS status Theorem for theBenchmark
% 2.07/0.63  % (26820)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.07/0.64  % (26818)Refutation not found, incomplete strategy% (26818)------------------------------
% 2.07/0.64  % (26818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (26804)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.07/0.64  % SZS output start Proof for theBenchmark
% 2.07/0.64  fof(f2065,plain,(
% 2.07/0.64    $false),
% 2.07/0.64    inference(subsumption_resolution,[],[f2064,f1471])).
% 2.07/0.64  fof(f1471,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(k4_xboole_0(sK2,X0),sK3)) )),
% 2.07/0.64    inference(subsumption_resolution,[],[f1468,f83])).
% 2.07/0.64  fof(f83,plain,(
% 2.07/0.64    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X2))) )),
% 2.07/0.64    inference(superposition,[],[f68,f48])).
% 2.07/0.64  fof(f48,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f2])).
% 2.07/0.64  fof(f2,axiom,(
% 2.07/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.07/0.64  fof(f68,plain,(
% 2.07/0.64    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.07/0.64    inference(backward_demodulation,[],[f44,f46])).
% 2.07/0.64  fof(f46,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f8])).
% 2.07/0.64  fof(f8,axiom,(
% 2.07/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.07/0.64  fof(f44,plain,(
% 2.07/0.64    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f7])).
% 2.07/0.64  fof(f7,axiom,(
% 2.07/0.64    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.07/0.64  fof(f1468,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(k4_xboole_0(sK2,X0),sK3) | ~m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(sK2))) )),
% 2.07/0.64    inference(superposition,[],[f1467,f340])).
% 2.07/0.64  fof(f340,plain,(
% 2.07/0.64    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_subset_1(X4,k3_xboole_0(X4,X5))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f335,f115])).
% 2.07/0.64  fof(f115,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.07/0.64    inference(backward_demodulation,[],[f81,f107])).
% 2.07/0.64  fof(f107,plain,(
% 2.07/0.64    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.07/0.64    inference(superposition,[],[f76,f79])).
% 2.07/0.64  fof(f79,plain,(
% 2.07/0.64    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 2.07/0.64    inference(superposition,[],[f73,f47])).
% 2.07/0.64  fof(f47,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f11])).
% 2.07/0.64  fof(f11,axiom,(
% 2.07/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.07/0.64  fof(f73,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 2.07/0.64    inference(superposition,[],[f47,f45])).
% 2.07/0.64  fof(f45,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f3])).
% 2.07/0.64  fof(f3,axiom,(
% 2.07/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.07/0.64  fof(f76,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 2.07/0.64    inference(resolution,[],[f49,f72])).
% 2.07/0.64  fof(f72,plain,(
% 2.07/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.07/0.64    inference(resolution,[],[f60,f68])).
% 2.07/0.64  fof(f60,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f23])).
% 2.07/0.64  fof(f23,plain,(
% 2.07/0.64    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.07/0.64    inference(ennf_transformation,[],[f16])).
% 2.07/0.64  fof(f16,plain,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.07/0.64    inference(unused_predicate_definition_removal,[],[f12])).
% 2.07/0.64  fof(f12,axiom,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.07/0.64  fof(f49,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f19])).
% 2.07/0.64  fof(f19,plain,(
% 2.07/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f1])).
% 2.07/0.64  fof(f1,axiom,(
% 2.07/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.07/0.64  fof(f81,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.07/0.64    inference(superposition,[],[f48,f48])).
% 2.07/0.64  fof(f335,plain,(
% 2.07/0.64    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k3_subset_1(X4,k3_xboole_0(X4,X5))) )),
% 2.07/0.64    inference(resolution,[],[f50,f83])).
% 2.07/0.64  fof(f50,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f20])).
% 2.07/0.64  fof(f20,plain,(
% 2.07/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.07/0.64    inference(ennf_transformation,[],[f6])).
% 2.07/0.64  fof(f6,axiom,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.07/0.64  fof(f1467,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(k3_subset_1(sK2,X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(sK2))) )),
% 2.07/0.64    inference(subsumption_resolution,[],[f1465,f69])).
% 2.07/0.64  fof(f69,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.07/0.64    inference(superposition,[],[f43,f66])).
% 2.07/0.64  fof(f66,plain,(
% 2.07/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.07/0.64    inference(equality_resolution,[],[f63])).
% 2.07/0.64  fof(f63,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.07/0.64    inference(cnf_transformation,[],[f39])).
% 2.07/0.64  fof(f39,plain,(
% 2.07/0.64    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.07/0.64    inference(flattening,[],[f38])).
% 2.07/0.64  fof(f38,plain,(
% 2.07/0.64    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.07/0.64    inference(nnf_transformation,[],[f4])).
% 2.07/0.64  fof(f4,axiom,(
% 2.07/0.64    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.07/0.64  fof(f43,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f5])).
% 2.07/0.64  fof(f5,axiom,(
% 2.07/0.64    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 2.07/0.64  fof(f1465,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(k3_subset_1(sK2,X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(sK2)) | r2_hidden(X0,k1_xboole_0)) )),
% 2.07/0.64    inference(resolution,[],[f55,f1205])).
% 2.07/0.64  fof(f1205,plain,(
% 2.07/0.64    sP0(sK3,sK2,k1_xboole_0)),
% 2.07/0.64    inference(subsumption_resolution,[],[f708,f1201])).
% 2.07/0.64  fof(f1201,plain,(
% 2.07/0.64    sP1(k1_xboole_0,sK2,sK3)),
% 2.07/0.64    inference(resolution,[],[f1196,f648])).
% 2.07/0.64  fof(f648,plain,(
% 2.07/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.07/0.64    inference(subsumption_resolution,[],[f647,f40])).
% 2.07/0.64  fof(f40,plain,(
% 2.07/0.64    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.07/0.64    inference(cnf_transformation,[],[f30])).
% 2.07/0.64  fof(f30,plain,(
% 2.07/0.64    k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.07/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f29])).
% 2.07/0.64  fof(f29,plain,(
% 2.07/0.64    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 2.07/0.64    introduced(choice_axiom,[])).
% 2.07/0.64  fof(f18,plain,(
% 2.07/0.64    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.07/0.64    inference(flattening,[],[f17])).
% 2.07/0.64  fof(f17,plain,(
% 2.07/0.64    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.07/0.64    inference(ennf_transformation,[],[f15])).
% 2.07/0.64  fof(f15,negated_conjecture,(
% 2.07/0.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 2.07/0.64    inference(negated_conjecture,[],[f14])).
% 2.07/0.64  fof(f14,conjecture,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 2.07/0.64  fof(f647,plain,(
% 2.07/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.07/0.64    inference(superposition,[],[f51,f42])).
% 2.07/0.64  fof(f42,plain,(
% 2.07/0.64    k1_xboole_0 = k7_setfam_1(sK2,sK3)),
% 2.07/0.64    inference(cnf_transformation,[],[f30])).
% 2.07/0.64  fof(f51,plain,(
% 2.07/0.64    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f21])).
% 2.07/0.64  fof(f21,plain,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.07/0.64    inference(ennf_transformation,[],[f10])).
% 2.07/0.64  fof(f10,axiom,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 2.07/0.64  fof(f1196,plain,(
% 2.07/0.64    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(sK2))) | sP1(X13,sK2,sK3)) )),
% 2.07/0.64    inference(resolution,[],[f59,f40])).
% 2.07/0.64  fof(f59,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP1(X2,X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f28])).
% 2.07/0.64  fof(f28,plain,(
% 2.07/0.64    ! [X0,X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.07/0.64    inference(definition_folding,[],[f22,f27,f26])).
% 2.07/0.64  fof(f26,plain,(
% 2.07/0.64    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 2.07/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.07/0.64  fof(f27,plain,(
% 2.07/0.64    ! [X2,X0,X1] : ((k7_setfam_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 2.07/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.07/0.64  fof(f22,plain,(
% 2.07/0.64    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.07/0.64    inference(ennf_transformation,[],[f9])).
% 2.07/0.64  fof(f9,axiom,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 2.07/0.64  fof(f708,plain,(
% 2.07/0.64    ~sP1(k1_xboole_0,sK2,sK3) | sP0(sK3,sK2,k1_xboole_0)),
% 2.07/0.64    inference(superposition,[],[f65,f42])).
% 2.07/0.64  fof(f65,plain,(
% 2.07/0.64    ( ! [X2,X1] : (~sP1(k7_setfam_1(X1,X2),X1,X2) | sP0(X2,X1,k7_setfam_1(X1,X2))) )),
% 2.07/0.64    inference(equality_resolution,[],[f52])).
% 2.07/0.64  fof(f52,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k7_setfam_1(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f32])).
% 2.07/0.64  fof(f32,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (((k7_setfam_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k7_setfam_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 2.07/0.64    inference(rectify,[],[f31])).
% 2.07/0.64  fof(f31,plain,(
% 2.07/0.64    ! [X2,X0,X1] : (((k7_setfam_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k7_setfam_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 2.07/0.64    inference(nnf_transformation,[],[f27])).
% 2.07/0.64  fof(f55,plain,(
% 2.07/0.64    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | r2_hidden(X4,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f37])).
% 2.07/0.64  fof(f37,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 2.07/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.07/0.64  fof(f36,plain,(
% 2.07/0.64    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1))) => ((~r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1))))),
% 2.07/0.64    introduced(choice_axiom,[])).
% 2.07/0.64  fof(f35,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 2.07/0.64    inference(rectify,[],[f34])).
% 2.07/0.64  fof(f34,plain,(
% 2.07/0.64    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 2.07/0.64    inference(flattening,[],[f33])).
% 2.07/0.64  fof(f33,plain,(
% 2.07/0.64    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 2.07/0.64    inference(nnf_transformation,[],[f26])).
% 2.07/0.64  fof(f2064,plain,(
% 2.07/0.64    r2_hidden(k4_xboole_0(sK2,sK4(sK3,sK2,sK3)),sK3)),
% 2.07/0.64    inference(forward_demodulation,[],[f2063,f2038])).
% 2.07/0.64  fof(f2038,plain,(
% 2.07/0.64    k4_xboole_0(sK2,sK4(sK3,sK2,sK3)) = k3_subset_1(sK2,sK4(sK3,sK2,sK3))),
% 2.07/0.64    inference(superposition,[],[f340,f2007])).
% 2.07/0.64  fof(f2007,plain,(
% 2.07/0.64    sK4(sK3,sK2,sK3) = k3_xboole_0(sK2,sK4(sK3,sK2,sK3))),
% 2.07/0.64    inference(resolution,[],[f430,f1209])).
% 2.07/0.64  fof(f1209,plain,(
% 2.07/0.64    ~sP0(sK3,sK2,sK3)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1208,f41])).
% 2.07/0.64  fof(f41,plain,(
% 2.07/0.64    k1_xboole_0 != sK3),
% 2.07/0.64    inference(cnf_transformation,[],[f30])).
% 2.07/0.64  fof(f1208,plain,(
% 2.07/0.64    k1_xboole_0 = sK3 | ~sP0(sK3,sK2,sK3)),
% 2.07/0.64    inference(forward_demodulation,[],[f1207,f42])).
% 2.07/0.64  fof(f1207,plain,(
% 2.07/0.64    ~sP0(sK3,sK2,sK3) | sK3 = k7_setfam_1(sK2,sK3)),
% 2.07/0.64    inference(resolution,[],[f1203,f53])).
% 2.07/0.64  fof(f53,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | k7_setfam_1(X1,X2) = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f32])).
% 2.07/0.64  fof(f1203,plain,(
% 2.07/0.64    sP1(sK3,sK2,sK3)),
% 2.07/0.64    inference(resolution,[],[f1196,f40])).
% 2.07/0.64  fof(f430,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | sK4(X0,X1,X2) = k3_xboole_0(X1,sK4(X0,X1,X2))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f429,f79])).
% 2.07/0.64  fof(f429,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | sK4(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),X1)) )),
% 2.07/0.64    inference(resolution,[],[f428,f49])).
% 2.07/0.64  fof(f428,plain,(
% 2.07/0.64    ( ! [X4,X5,X3] : (r1_tarski(sK4(X3,X4,X5),X4) | sP0(X3,X4,X5)) )),
% 2.07/0.64    inference(resolution,[],[f56,f60])).
% 2.07/0.64  fof(f56,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1)) | sP0(X0,X1,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f37])).
% 2.07/0.64  fof(f2063,plain,(
% 2.07/0.64    r2_hidden(k3_subset_1(sK2,sK4(sK3,sK2,sK3)),sK3)),
% 2.07/0.64    inference(subsumption_resolution,[],[f2061,f1209])).
% 2.07/0.64  fof(f2061,plain,(
% 2.07/0.64    r2_hidden(k3_subset_1(sK2,sK4(sK3,sK2,sK3)),sK3) | sP0(sK3,sK2,sK3)),
% 2.07/0.64    inference(resolution,[],[f2013,f57])).
% 2.07/0.64  fof(f57,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f37])).
% 2.07/0.64  fof(f2013,plain,(
% 2.07/0.64    ~r2_hidden(sK4(sK3,sK2,sK3),sK3)),
% 2.07/0.64    inference(superposition,[],[f1472,f2007])).
% 2.07/0.64  fof(f1472,plain,(
% 2.07/0.64    ( ! [X2] : (~r2_hidden(k3_xboole_0(sK2,X2),sK3)) )),
% 2.07/0.64    inference(subsumption_resolution,[],[f1470,f68])).
% 2.07/0.64  fof(f1470,plain,(
% 2.07/0.64    ( ! [X2] : (~r2_hidden(k3_xboole_0(sK2,X2),sK3) | ~m1_subset_1(k4_xboole_0(sK2,X2),k1_zfmisc_1(sK2))) )),
% 2.07/0.64    inference(superposition,[],[f1467,f338])).
% 2.07/0.64  fof(f338,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f333,f48])).
% 2.07/0.64  fof(f333,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 2.07/0.64    inference(resolution,[],[f50,f68])).
% 2.07/0.64  % SZS output end Proof for theBenchmark
% 2.07/0.64  % (26803)------------------------------
% 2.07/0.64  % (26803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (26803)Termination reason: Refutation
% 2.07/0.64  
% 2.07/0.64  % (26803)Memory used [KB]: 7291
% 2.07/0.64  % (26803)Time elapsed: 0.147 s
% 2.07/0.64  % (26803)------------------------------
% 2.07/0.64  % (26803)------------------------------
% 2.07/0.64  % (26818)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.64  
% 2.07/0.64  % (26818)Memory used [KB]: 10746
% 2.07/0.64  % (26818)Time elapsed: 0.220 s
% 2.07/0.64  % (26818)------------------------------
% 2.07/0.64  % (26818)------------------------------
% 2.07/0.64  % (26789)Success in time 0.282 s
%------------------------------------------------------------------------------
