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
% DateTime   : Thu Dec  3 12:46:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 145 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  229 ( 413 expanded)
%              Number of equality atoms :   51 ( 140 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(subsumption_resolution,[],[f257,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f257,plain,(
    ! [X5] : ~ r1_xboole_0(k2_tarski(k3_subset_1(sK2,sK4(sK3)),X5),k1_xboole_0) ),
    inference(resolution,[],[f252,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f252,plain,(
    r2_hidden(k3_subset_1(sK2,sK4(sK3)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f251,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f251,plain,
    ( r2_hidden(k3_subset_1(sK2,sK4(sK3)),k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f250,f163])).

fof(f163,plain,(
    m1_subset_1(sK4(sK3),k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f159,f44])).

fof(f159,plain,
    ( k1_xboole_0 = sK3
    | m1_subset_1(sK4(sK3),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f142,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f142,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | k1_xboole_0 = X5
      | m1_subset_1(sK4(X5),X6) ) ),
    inference(resolution,[],[f139,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f139,plain,(
    ! [X7] :
      ( r2_hidden(sK4(X7),X7)
      | k1_xboole_0 = X7 ) ),
    inference(subsumption_resolution,[],[f132,f46])).

fof(f132,plain,(
    ! [X8,X7] :
      ( r2_hidden(sK4(X7),X7)
      | k1_xboole_0 = X7
      | ~ r1_xboole_0(k2_tarski(sK4(X7),X8),k1_xboole_0) ) ),
    inference(resolution,[],[f121,f65])).

fof(f121,plain,(
    ! [X1] :
      ( r2_hidden(sK4(X1),k1_xboole_0)
      | r2_hidden(sK4(X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f118,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f114,f72])).

fof(f72,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f71,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f50,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,k3_subset_1(X1,k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f51,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | r2_hidden(X2,k3_subset_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f250,plain,
    ( r2_hidden(k3_subset_1(sK2,sK4(sK3)),k1_xboole_0)
    | ~ m1_subset_1(sK4(sK3),k1_zfmisc_1(sK2))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f141,f103])).

fof(f103,plain,(
    sP0(k1_xboole_0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f80,f100])).

fof(f100,plain,(
    sP1(sK3,sK2,k1_xboole_0) ),
    inference(resolution,[],[f84,f43])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | sP1(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP1(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X2,X0,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f25,f30,f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> r2_hidden(k3_subset_1(X0,X3),X1) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f80,plain,
    ( ~ sP1(sK3,sK2,k1_xboole_0)
    | sP0(k1_xboole_0,sK2,sK3) ),
    inference(superposition,[],[f70,f77])).

fof(f77,plain,(
    sK3 = k7_setfam_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f74,f45])).

fof(f45,plain,(
    k1_xboole_0 = k7_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    sK3 = k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f70,plain,(
    ! [X2,X1] :
      ( ~ sP1(k7_setfam_1(X1,X2),X1,X2)
      | sP0(X2,X1,k7_setfam_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k7_setfam_1(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k7_setfam_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f141,plain,(
    ! [X4,X2,X3] :
      ( ~ sP0(X4,X3,X2)
      | r2_hidden(k3_subset_1(X3,sK4(X2)),X4)
      | ~ m1_subset_1(sK4(X2),k1_zfmisc_1(X3))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f139,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k3_subset_1(X1,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) )
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X2)
                | ~ r2_hidden(k3_subset_1(X1,X4),X0) )
              & ( r2_hidden(k3_subset_1(X1,X4),X0)
                | ~ r2_hidden(X4,X2) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X1,X3),X0)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X1,X3),X0)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ( ~ r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:19:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (25782)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.49  % (25775)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (25801)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.50  % (25782)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (25801)Refutation not found, incomplete strategy% (25801)------------------------------
% 0.22/0.50  % (25801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f257,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ( ! [X5] : (~r1_xboole_0(k2_tarski(k3_subset_1(sK2,sK4(sK3)),X5),k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f252,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    r2_hidden(k3_subset_1(sK2,sK4(sK3)),k1_xboole_0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f251,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    k1_xboole_0 != sK3),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f18])).
% 0.22/0.51  fof(f18,conjecture,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    r2_hidden(k3_subset_1(sK2,sK4(sK3)),k1_xboole_0) | k1_xboole_0 = sK3),
% 0.22/0.51    inference(subsumption_resolution,[],[f250,f163])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    m1_subset_1(sK4(sK3),k1_zfmisc_1(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f159,f44])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    k1_xboole_0 = sK3 | m1_subset_1(sK4(sK3),k1_zfmisc_1(sK2))),
% 0.22/0.51    inference(resolution,[],[f142,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(X6)) | k1_xboole_0 = X5 | m1_subset_1(sK4(X5),X6)) )),
% 0.22/0.51    inference(resolution,[],[f139,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X7] : (r2_hidden(sK4(X7),X7) | k1_xboole_0 = X7) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f46])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X8,X7] : (r2_hidden(sK4(X7),X7) | k1_xboole_0 = X7 | ~r1_xboole_0(k2_tarski(sK4(X7),X8),k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f121,f65])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X1] : (r2_hidden(sK4(X1),k1_xboole_0) | r2_hidden(sK4(X1),X1) | k1_xboole_0 = X1) )),
% 0.22/0.51    inference(resolution,[],[f118,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.51    inference(forward_demodulation,[],[f114,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(forward_demodulation,[],[f71,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f50,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(X0,X1) | r2_hidden(X0,k3_subset_1(X1,k1_xboole_0)) | k1_xboole_0 = X1) )),
% 0.22/0.51    inference(resolution,[],[f51,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | r2_hidden(X2,k3_subset_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    r2_hidden(k3_subset_1(sK2,sK4(sK3)),k1_xboole_0) | ~m1_subset_1(sK4(sK3),k1_zfmisc_1(sK2)) | k1_xboole_0 = sK3),
% 0.22/0.51    inference(resolution,[],[f141,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    sP0(k1_xboole_0,sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f80,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    sP1(sK3,sK2,k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f84,f43])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | sP1(X0,X1,k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f62,f49])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP1(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(definition_folding,[],[f25,f30,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X2,X0,X1] : ((k7_setfam_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ~sP1(sK3,sK2,k1_xboole_0) | sP0(k1_xboole_0,sK2,sK3)),
% 0.22/0.51    inference(superposition,[],[f70,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    sK3 = k7_setfam_1(sK2,k1_xboole_0)),
% 0.22/0.51    inference(forward_demodulation,[],[f74,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    k1_xboole_0 = k7_setfam_1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    sK3 = k7_setfam_1(sK2,k7_setfam_1(sK2,sK3))),
% 0.22/0.51    inference(resolution,[],[f54,f43])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~sP1(k7_setfam_1(X1,X2),X1,X2) | sP0(X2,X1,k7_setfam_1(X1,X2))) )),
% 0.22/0.51    inference(equality_resolution,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k7_setfam_1(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((k7_setfam_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k7_setfam_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 0.22/0.51    inference(rectify,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X2,X0,X1] : (((k7_setfam_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k7_setfam_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f30])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (~sP0(X4,X3,X2) | r2_hidden(k3_subset_1(X3,sK4(X2)),X4) | ~m1_subset_1(sK4(X2),k1_zfmisc_1(X3)) | k1_xboole_0 = X2) )),
% 0.22/0.51    inference(resolution,[],[f139,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(k3_subset_1(X1,X4),X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | r2_hidden(sK5(X0,X1,X2),X2)) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1))) => ((~r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | r2_hidden(sK5(X0,X1,X2),X2)) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 0.22/0.51    inference(flattening,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 0.22/0.51    inference(nnf_transformation,[],[f29])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (25782)------------------------------
% 0.22/0.51  % (25782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25782)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (25782)Memory used [KB]: 6652
% 0.22/0.51  % (25782)Time elapsed: 0.095 s
% 0.22/0.51  % (25782)------------------------------
% 0.22/0.51  % (25782)------------------------------
% 0.22/0.52  % (25774)Success in time 0.152 s
%------------------------------------------------------------------------------
