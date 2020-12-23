%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 147 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  278 ( 546 expanded)
%              Number of equality atoms :   92 ( 105 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f300,plain,(
    ~ r1_tarski(k1_xboole_0,sK3) ),
    inference(resolution,[],[f298,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f298,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(resolution,[],[f284,f127])).

fof(f127,plain,(
    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_xboole_0) ),
    inference(superposition,[],[f126,f97])).

fof(f97,plain,(
    k1_xboole_0 = k1_tarski(sK3) ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f95,plain,(
    v1_xboole_0(k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f94,f47])).

fof(f47,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( v1_zfmisc_1(sK2)
    & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    & m1_subset_1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK2)
          & v1_subset_1(k6_domain_1(sK2,X1),sK2)
          & m1_subset_1(X1,sK2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK2)
        & v1_subset_1(k6_domain_1(sK2,X1),sK2)
        & m1_subset_1(X1,sK2) )
   => ( v1_zfmisc_1(sK2)
      & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
      & m1_subset_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f94,plain,
    ( v1_xboole_0(k1_tarski(sK3))
    | ~ v1_zfmisc_1(sK2) ),
    inference(subsumption_resolution,[],[f91,f87])).

fof(f87,plain,(
    v1_subset_1(k1_tarski(sK3),sK2) ),
    inference(backward_demodulation,[],[f46,f86])).

fof(f86,plain,(
    k6_domain_1(sK2,sK3) = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f85,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( k6_domain_1(sK2,sK3) = k1_tarski(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f46,plain,(
    v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,
    ( v1_xboole_0(k1_tarski(sK3))
    | ~ v1_subset_1(k1_tarski(sK3),sK2)
    | ~ v1_zfmisc_1(sK2) ),
    inference(resolution,[],[f90,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f90,plain,(
    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(sK2)) ),
    inference(forward_demodulation,[],[f89,f86])).

fof(f89,plain,(
    m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f88,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f126,plain,(
    ! [X0] : sP1(X0,X0,X0,X0,X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f125,f49])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f125,plain,(
    ! [X0,X1] : sP1(X0,X0,X0,X0,X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f124,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f124,plain,(
    ! [X2,X0,X1] : sP1(X0,X0,X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f123,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f123,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X0,X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f122,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f122,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X0,X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f121,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f121,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f83,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(definition_folding,[],[f29,f31,f30])).

fof(f30,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(f284,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP1(X2,X3,X4,X5,X6,X7,X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f63,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X9,X7)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X8,X7) )
          & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X8,X7) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(nnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (2021)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (2013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (2005)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (2013)Refutation not found, incomplete strategy% (2013)------------------------------
% 0.21/0.51  % (2013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1999)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (2013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2013)Memory used [KB]: 6268
% 0.21/0.51  % (2013)Time elapsed: 0.056 s
% 0.21/0.51  % (2013)------------------------------
% 0.21/0.51  % (2013)------------------------------
% 0.21/0.52  % (2000)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (2001)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (2002)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (2002)Refutation not found, incomplete strategy% (2002)------------------------------
% 0.21/0.52  % (2002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2002)Memory used [KB]: 6140
% 0.21/0.52  % (2002)Time elapsed: 0.108 s
% 0.21/0.52  % (2002)------------------------------
% 0.21/0.52  % (2002)------------------------------
% 0.21/0.52  % (2011)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (2004)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (2005)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f300,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,sK3)),
% 0.21/0.53    inference(resolution,[],[f298,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    r2_hidden(sK3,k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f284,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_xboole_0)),
% 0.21/0.53    inference(superposition,[],[f126,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.53    inference(resolution,[],[f95,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    v1_xboole_0(k1_tarski(sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f94,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v1_zfmisc_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2)) & ~v1_xboole_0(sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f34,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) & ~v1_xboole_0(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) => (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    v1_xboole_0(k1_tarski(sK3)) | ~v1_zfmisc_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    v1_subset_1(k1_tarski(sK3),sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f46,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    k6_domain_1(sK2,sK3) = k1_tarski(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f85,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    k6_domain_1(sK2,sK3) = k1_tarski(sK3) | v1_xboole_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f54,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    m1_subset_1(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_subset_1(k6_domain_1(sK2,sK3),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    v1_xboole_0(k1_tarski(sK3)) | ~v1_subset_1(k1_tarski(sK3),sK2) | ~v1_zfmisc_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f90,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f52,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f89,f86])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f88,f44])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) | v1_xboole_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f55,f45])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X0] : (sP1(X0,X0,X0,X0,X0,X0,X0,k1_tarski(X0))) )),
% 0.21/0.53    inference(superposition,[],[f125,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP1(X0,X0,X0,X0,X0,X0,X1,k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(superposition,[],[f124,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP1(X0,X0,X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.53    inference(superposition,[],[f123,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sP1(X0,X0,X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.53    inference(superposition,[],[f122,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X0,X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 0.21/0.53    inference(superposition,[],[f121,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.21/0.53    inference(superposition,[],[f83,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.53    inference(equality_resolution,[],[f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 0.21/0.53    inference(nnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.53    inference(definition_folding,[],[f29,f31,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : (sP0(X8,X6,X5,X4,X3,X2,X1,X0) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP1(X2,X3,X4,X5,X6,X7,X0,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f63,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.21/0.53    inference(equality_resolution,[],[f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(rectify,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.53    inference(flattening,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f30])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (~sP0(X9,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X7) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(rectify,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(nnf_transformation,[],[f31])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2005)------------------------------
% 0.21/0.53  % (2005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2005)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2005)Memory used [KB]: 6524
% 0.21/0.53  % (2005)Time elapsed: 0.073 s
% 0.21/0.53  % (2005)------------------------------
% 0.21/0.53  % (2005)------------------------------
% 0.21/0.54  % (1997)Success in time 0.171 s
%------------------------------------------------------------------------------
