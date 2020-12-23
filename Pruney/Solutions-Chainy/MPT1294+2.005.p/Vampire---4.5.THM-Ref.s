%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 220 expanded)
%              Number of leaves         :   15 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  250 ( 582 expanded)
%              Number of equality atoms :   62 ( 169 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(subsumption_resolution,[],[f85,f142])).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f106,f140])).

fof(f140,plain,(
    ! [X3] : sP0(k1_xboole_0,X3,k1_xboole_0) ),
    inference(resolution,[],[f133,f130])).

fof(f130,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f66,f128])).

fof(f128,plain,(
    ! [X3] : r1_xboole_0(k1_xboole_0,X3) ),
    inference(subsumption_resolution,[],[f127,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_xboole_0,X1)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f68,f66])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f45,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f61,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f127,plain,(
    ! [X3] :
      ( r1_xboole_0(k1_xboole_0,sK4(k1_xboole_0,X3))
      | r1_xboole_0(k1_xboole_0,X3) ) ),
    inference(resolution,[],[f124,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(k1_xboole_0,X0),X1)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f70,f68])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f121,f42])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f46,f65])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK5(k1_xboole_0,X8,X9),X9)
      | sP0(k1_xboole_0,X8,X9) ) ),
    inference(resolution,[],[f55,f130])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> r2_hidden(k3_subset_1(X0,X3),X1) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f106,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f103,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k7_setfam_1(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k7_setfam_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f103,plain,(
    ! [X0] : sP1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f100,f42])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | sP1(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP1(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X2,X0,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f18,f22,f21])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f85,plain,(
    k1_xboole_0 != k7_setfam_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f60,f84])).

fof(f84,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( k1_xboole_0 = sK3
        & k1_xboole_0 != k7_setfam_1(sK2,sK3) )
      | ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
        & k1_xboole_0 != sK3 ) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
          | ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ( k1_xboole_0 = sK3
          & k1_xboole_0 != k7_setfam_1(sK2,sK3) )
        | ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
          & k1_xboole_0 != sK3 ) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

fof(f83,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,
    ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f60,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k7_setfam_1(sK2,k1_xboole_0) ),
    inference(inner_rewriting,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k7_setfam_1(sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:26:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5435)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.48  % (5435)Refutation not found, incomplete strategy% (5435)------------------------------
% 0.22/0.48  % (5435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5435)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5435)Memory used [KB]: 1663
% 0.22/0.48  % (5435)Time elapsed: 0.084 s
% 0.22/0.48  % (5435)------------------------------
% 0.22/0.48  % (5435)------------------------------
% 0.22/0.49  % (5458)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.49  % (5450)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.49  % (5450)Refutation not found, incomplete strategy% (5450)------------------------------
% 0.22/0.49  % (5450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5450)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (5450)Memory used [KB]: 6140
% 0.22/0.49  % (5450)Time elapsed: 0.004 s
% 0.22/0.49  % (5450)------------------------------
% 0.22/0.49  % (5450)------------------------------
% 0.22/0.49  % (5442)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (5442)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ( ! [X3] : (sP0(k1_xboole_0,X3,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f133,f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f128])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f127,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X1) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f68,f66])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(superposition,[],[f45,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f61,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.50    inference(superposition,[],[f44,f43])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X3] : (r1_xboole_0(k1_xboole_0,sK4(k1_xboole_0,X3)) | r1_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.50    inference(resolution,[],[f124,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(k1_xboole_0,X0),X1) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f70,f68])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f58,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f121,f42])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(resolution,[],[f48,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(superposition,[],[f46,f65])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X8,X9] : (r2_hidden(sK5(k1_xboole_0,X8,X9),X9) | sP0(k1_xboole_0,X8,X9)) )),
% 0.22/0.50    inference(resolution,[],[f55,f130])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | r2_hidden(sK5(X0,X1,X2),X2)) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1))) => ((~r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK5(X0,X1,X2)),X0) | r2_hidden(sK5(X0,X1,X2),X2)) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(rectify,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 0.22/0.50    inference(flattening,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X0] : (~sP0(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = k7_setfam_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f103,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | k7_setfam_1(X1,X2) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((k7_setfam_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k7_setfam_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 0.22/0.50    inference(rectify,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X2,X0,X1] : (((k7_setfam_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k7_setfam_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X2,X0,X1] : ((k7_setfam_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0] : (sP1(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f100,f42])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | sP1(X0,X1,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f57,f42])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP1(X2,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(definition_folding,[],[f18,f22,f21])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    k1_xboole_0 != k7_setfam_1(sK2,k1_xboole_0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f60,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    k1_xboole_0 = sK3),
% 0.22/0.50    inference(subsumption_resolution,[],[f83,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ((k1_xboole_0 = sK3 & k1_xboole_0 != k7_setfam_1(sK2,sK3)) | (k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (((k1_xboole_0 = sK3 & k1_xboole_0 != k7_setfam_1(sK2,sK3)) | (k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) | k1_xboole_0 = sK3),
% 0.22/0.50    inference(superposition,[],[f49,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    k1_xboole_0 = k7_setfam_1(sK2,sK3) | k1_xboole_0 = sK3),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    k1_xboole_0 != sK3 | k1_xboole_0 != k7_setfam_1(sK2,k1_xboole_0)),
% 0.22/0.50    inference(inner_rewriting,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    k1_xboole_0 != k7_setfam_1(sK2,sK3) | k1_xboole_0 != sK3),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (5442)------------------------------
% 0.22/0.50  % (5442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5442)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (5442)Memory used [KB]: 6268
% 0.22/0.50  % (5442)Time elapsed: 0.110 s
% 0.22/0.50  % (5442)------------------------------
% 0.22/0.50  % (5442)------------------------------
% 0.22/0.50  % (5434)Success in time 0.141 s
%------------------------------------------------------------------------------
