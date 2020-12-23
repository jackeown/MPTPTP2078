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

% Result     : Theorem 0.20s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 124 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  274 ( 457 expanded)
%              Number of equality atoms :   75 (  82 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(subsumption_resolution,[],[f140,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( v1_zfmisc_1(sK2)
    & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    & m1_subset_1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK2)
        & v1_subset_1(k6_domain_1(sK2,X1),sK2)
        & m1_subset_1(X1,sK2) )
   => ( v1_zfmisc_1(sK2)
      & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
      & m1_subset_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f140,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f137,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f131,f107])).

fof(f107,plain,(
    v1_xboole_0(k6_domain_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f106,f42])).

fof(f106,plain,
    ( v1_xboole_0(k6_domain_1(sK2,sK3))
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f105,f43])).

fof(f105,plain,
    ( v1_xboole_0(k6_domain_1(sK2,sK3))
    | ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f45,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,
    ( v1_xboole_0(k6_domain_1(sK2,sK3))
    | ~ v1_zfmisc_1(sK2)
    | ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f87,f44])).

fof(f44,plain,(
    v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | v1_xboole_0(k6_domain_1(X0,X1))
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f86,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k6_domain_1(X0,X1))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f129,f77])).

fof(f77,plain,(
    ! [X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( sP0(X6,X4,X3,X2,X1,X0)
    <=> ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X0,X0,X0,X0,X0)
      | ~ v1_xboole_0(k6_domain_1(X1,X0))
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f126,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

% (10367)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_xboole_0(k4_enumset1(X5,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(resolution,[],[f123,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f46,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f123,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ r1_tarski(k4_enumset1(X11,X11,X10,X9,X8,X7),X6)
      | ~ sP0(X6,X7,X8,X9,X10,X11) ) ),
    inference(resolution,[],[f120,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,k4_enumset1(X5,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(resolution,[],[f59,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X1,X2,X3,X4,k4_enumset1(X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f68,f57])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP1(X0,X1,X2,X3,X4,X5) )
      & ( sP1(X0,X1,X2,X3,X4,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(definition_folding,[],[f27,f29,f28])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP1(X0,X1,X2,X3,X4,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5)
      | ~ sP0(X7,X4,X3,X2,X1,X0)
      | r2_hidden(X7,X5) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

% (10376)Termination reason: Refutation not found, incomplete strategy

% (10376)Memory used [KB]: 10746
% (10376)Time elapsed: 0.084 s
% (10376)------------------------------
% (10376)------------------------------
% (10360)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (10358)Refutation not found, incomplete strategy% (10358)------------------------------
% (10358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10358)Termination reason: Refutation not found, incomplete strategy

% (10358)Memory used [KB]: 6140
% (10358)Time elapsed: 0.125 s
% (10358)------------------------------
% (10358)------------------------------
% (10365)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (10380)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (10365)Refutation not found, incomplete strategy% (10365)------------------------------
% (10365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10365)Termination reason: Refutation not found, incomplete strategy

% (10365)Memory used [KB]: 10618
% (10365)Time elapsed: 0.126 s
% (10365)------------------------------
% (10365)------------------------------
% (10354)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (10374)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (10372)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (10373)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (10364)Refutation not found, incomplete strategy% (10364)------------------------------
% (10364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10364)Termination reason: Refutation not found, incomplete strategy

% (10364)Memory used [KB]: 10618
% (10364)Time elapsed: 0.131 s
% (10364)------------------------------
% (10364)------------------------------
% (10357)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (10377)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (10370)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (10378)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (10366)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (10356)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (10382)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f36,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X6,X5) )
          & ( sP0(X6,X4,X3,X2,X1,X0)
            | r2_hidden(X6,X5) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ~ sP0(X6,X4,X3,X2,X1,X0) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(nnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (10355)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (10359)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (10364)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (10376)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (10371)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (10358)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (10381)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (10371)Refutation not found, incomplete strategy% (10371)------------------------------
% 0.20/0.52  % (10371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10376)Refutation not found, incomplete strategy% (10376)------------------------------
% 0.20/0.52  % (10376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10371)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10371)Memory used [KB]: 10618
% 0.20/0.52  % (10371)Time elapsed: 0.082 s
% 0.20/0.52  % (10371)------------------------------
% 0.20/0.52  % (10371)------------------------------
% 0.20/0.52  % (10381)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f140,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ~v1_xboole_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2)) & ~v1_xboole_0(sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f32,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) & ~v1_xboole_0(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) => (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.52    inference(negated_conjecture,[],[f14])).
% 0.20/0.52  fof(f14,conjecture,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    v1_xboole_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f137,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    m1_subset_1(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ~m1_subset_1(sK3,sK2) | v1_xboole_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f131,f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    v1_xboole_0(k6_domain_1(sK2,sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f106,f42])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    v1_xboole_0(k6_domain_1(sK2,sK3)) | v1_xboole_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f105,f43])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    v1_xboole_0(k6_domain_1(sK2,sK3)) | ~m1_subset_1(sK3,sK2) | v1_xboole_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f102,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    v1_zfmisc_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    v1_xboole_0(k6_domain_1(sK2,sK3)) | ~v1_zfmisc_1(sK2) | ~m1_subset_1(sK3,sK2) | v1_xboole_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f87,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    v1_subset_1(k6_domain_1(sK2,sK3),sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) | v1_xboole_0(k6_domain_1(X0,X1)) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(resolution,[],[f86,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f50,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k6_domain_1(X0,X1)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(resolution,[],[f129,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(equality_resolution,[],[f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 0.20/0.52    inference(rectify,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 0.20/0.52    inference(flattening,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X6,X4,X3,X2,X1,X0] : (sP0(X6,X4,X3,X2,X1,X0) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP0(X2,X0,X0,X0,X0,X0) | ~v1_xboole_0(k6_domain_1(X1,X0)) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.20/0.52    inference(superposition,[],[f126,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f52,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f47,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f51,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f55,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f56,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  % (10367)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_xboole_0(k4_enumset1(X5,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(resolution,[],[f123,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(superposition,[],[f46,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X6,X10,X8,X7,X11,X9] : (~r1_tarski(k4_enumset1(X11,X11,X10,X9,X8,X7),X6) | ~sP0(X6,X7,X8,X9,X10,X11)) )),
% 0.20/0.52    inference(resolution,[],[f120,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X0,k4_enumset1(X5,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(resolution,[],[f59,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4,k4_enumset1(X0,X0,X1,X2,X3,X4))) )),
% 0.20/0.52    inference(equality_resolution,[],[f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 0.20/0.52    inference(definition_unfolding,[],[f68,f57])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP1(X0,X1,X2,X3,X4,X5)) & (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.20/0.52    inference(nnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP1(X0,X1,X2,X3,X4,X5))),
% 0.20/0.52    inference(definition_folding,[],[f27,f29,f28])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : (sP1(X0,X1,X2,X3,X4,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> sP0(X6,X4,X3,X2,X1,X0)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5) | ~sP0(X7,X4,X3,X2,X1,X0) | r2_hidden(X7,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.20/0.53  % (10376)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10376)Memory used [KB]: 10746
% 0.20/0.53  % (10376)Time elapsed: 0.084 s
% 0.20/0.53  % (10376)------------------------------
% 0.20/0.53  % (10376)------------------------------
% 1.29/0.53  % (10360)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (10358)Refutation not found, incomplete strategy% (10358)------------------------------
% 1.29/0.53  % (10358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (10358)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (10358)Memory used [KB]: 6140
% 1.29/0.53  % (10358)Time elapsed: 0.125 s
% 1.29/0.53  % (10358)------------------------------
% 1.29/0.53  % (10358)------------------------------
% 1.29/0.53  % (10365)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.53  % (10380)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.53  % (10365)Refutation not found, incomplete strategy% (10365)------------------------------
% 1.29/0.53  % (10365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (10365)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (10365)Memory used [KB]: 10618
% 1.29/0.53  % (10365)Time elapsed: 0.126 s
% 1.29/0.53  % (10365)------------------------------
% 1.29/0.53  % (10365)------------------------------
% 1.29/0.53  % (10354)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (10374)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (10372)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.53  % (10373)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.53  % (10364)Refutation not found, incomplete strategy% (10364)------------------------------
% 1.29/0.53  % (10364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (10364)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (10364)Memory used [KB]: 10618
% 1.29/0.53  % (10364)Time elapsed: 0.131 s
% 1.29/0.53  % (10364)------------------------------
% 1.29/0.53  % (10364)------------------------------
% 1.29/0.53  % (10357)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (10377)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (10370)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  % (10378)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.54  % (10366)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (10356)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (10382)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  fof(f36,plain,(
% 1.29/0.54    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5))))),
% 1.29/0.54    introduced(choice_axiom,[])).
% 1.29/0.54  fof(f35,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.29/0.54    inference(rectify,[],[f34])).
% 1.29/0.54  fof(f34,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | ~sP0(X6,X4,X3,X2,X1,X0)) & (sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.29/0.54    inference(nnf_transformation,[],[f29])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (10381)------------------------------
% 1.29/0.54  % (10381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (10381)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (10381)Memory used [KB]: 6268
% 1.29/0.54  % (10381)Time elapsed: 0.119 s
% 1.29/0.54  % (10381)------------------------------
% 1.29/0.54  % (10381)------------------------------
% 1.29/0.54  % (10368)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.54  % (10353)Success in time 0.177 s
%------------------------------------------------------------------------------
