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
% DateTime   : Thu Dec  3 13:20:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 315 expanded)
%              Number of leaves         :   17 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  275 (1140 expanded)
%              Number of equality atoms :   56 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(subsumption_resolution,[],[f196,f129])).

fof(f129,plain,(
    sP2(sK4,sK3) ),
    inference(backward_demodulation,[],[f123,f125])).

fof(f125,plain,(
    sK4 = sK5(sK3) ),
    inference(resolution,[],[f123,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK3)
      | sK4 = X0 ) ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f88,plain,(
    r2_hidden(sK4,sK3) ),
    inference(subsumption_resolution,[],[f85,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( v1_zfmisc_1(sK3)
    & v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    & m1_subset_1(sK4,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK3)
          & v1_subset_1(k6_domain_1(sK3,X1),sK3)
          & m1_subset_1(X1,sK3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK3)
        & v1_subset_1(k6_domain_1(sK3,X1),sK3)
        & m1_subset_1(X1,sK3) )
   => ( v1_zfmisc_1(sK3)
      & v1_subset_1(k6_domain_1(sK3,sK4),sK3)
      & m1_subset_1(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f85,plain,
    ( r2_hidden(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f45,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f45,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f123,plain,(
    sP2(sK5(sK3),sK3) ),
    inference(superposition,[],[f68,f119])).

fof(f119,plain,(
    sK3 = k1_tarski(sK5(sK3)) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f118,plain,
    ( sK3 = k1_tarski(sK5(sK3))
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f114,f81])).

fof(f81,plain,(
    m1_subset_1(sK5(sK3),sK3) ),
    inference(resolution,[],[f80,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ( k6_domain_1(X0,sK5(X0)) = X0
          & m1_subset_1(sK5(X0),X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK5(X0)) = X0
        & m1_subset_1(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X2] :
            ( k6_domain_1(X0,X2) = X0
            & m1_subset_1(X2,X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ? [X1] :
          ( k6_domain_1(X0,X1) = X0
          & m1_subset_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f80,plain,(
    sP0(sK3) ),
    inference(subsumption_resolution,[],[f78,f47])).

fof(f47,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,
    ( sP0(sK3)
    | ~ v1_zfmisc_1(sK3) ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_zfmisc_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

% (32486)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f25,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f74,plain,(
    sP1(sK3) ),
    inference(resolution,[],[f44,f53])).

fof(f53,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f14,f25,f24])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f114,plain,
    ( sK3 = k1_tarski(sK5(sK3))
    | ~ m1_subset_1(sK5(sK3),sK3)
    | v1_xboole_0(sK3) ),
    inference(superposition,[],[f82,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f82,plain,(
    sK3 = k6_domain_1(sK3,sK5(sK3)) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK5(X0)) = X0
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0] : sP2(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP2(X0,X1) )
      & ( sP2(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP2(X0,X1) ) ),
    inference(definition_folding,[],[f1,f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f196,plain,(
    ~ sP2(sK4,sK3) ),
    inference(backward_demodulation,[],[f108,f195])).

fof(f195,plain,(
    sK3 = sK6(sK3) ),
    inference(subsumption_resolution,[],[f194,f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK6(X0),X0)
      & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f194,plain,
    ( sK3 = sK6(sK3)
    | ~ m1_subset_1(sK6(sK3),k1_zfmisc_1(sK3)) ),
    inference(resolution,[],[f168,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f168,plain,
    ( ~ r1_tarski(sK6(sK3),sK3)
    | sK3 = sK6(sK3) ),
    inference(resolution,[],[f161,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK3)
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f75,f44])).

fof(f75,plain,(
    ! [X0] :
      ( sK3 = X0
      | ~ r1_tarski(X0,sK3)
      | v1_xboole_0(sK3)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f47,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f161,plain,(
    ~ v1_xboole_0(sK6(sK3)) ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f160,plain,
    ( ~ v1_xboole_0(sK6(sK3))
    | ~ m1_subset_1(sK6(sK3),k1_zfmisc_1(sK3)) ),
    inference(resolution,[],[f73,f57])).

fof(f57,plain,(
    ! [X0] : ~ v1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X4] :
      ( v1_subset_1(X4,sK3)
      | ~ v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3)) ) ),
    inference(resolution,[],[f44,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f108,plain,(
    ~ sP2(sK4,sK6(sK3)) ),
    inference(resolution,[],[f93,f57])).

fof(f93,plain,(
    ! [X0] :
      ( v1_subset_1(X0,sK3)
      | ~ sP2(sK4,X0) ) ),
    inference(superposition,[],[f92,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    v1_subset_1(k1_tarski(sK4),sK3) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f91,plain,
    ( v1_subset_1(k1_tarski(sK4),sK3)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f90,f45])).

fof(f90,plain,
    ( v1_subset_1(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(superposition,[],[f46,f59])).

fof(f46,plain,(
    v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (32478)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (32478)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f196,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    sP2(sK4,sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f123,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    sK4 = sK5(sK3)),
% 0.21/0.49    inference(resolution,[],[f123,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (~sP2(X0,sK3) | sK4 = X0) )),
% 0.21/0.49    inference(resolution,[],[f88,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP2(X0,X1) | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP2(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    r2_hidden(sK4,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,sK4),sK3) & m1_subset_1(sK4,sK3)) & ~v1_xboole_0(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f30,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,X1),sK3) & m1_subset_1(X1,sK3)) & ~v1_xboole_0(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X1] : (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,X1),sK3) & m1_subset_1(X1,sK3)) => (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,sK4),sK3) & m1_subset_1(sK4,sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    r2_hidden(sK4,sK3) | v1_xboole_0(sK3)),
% 0.21/0.49    inference(resolution,[],[f45,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    m1_subset_1(sK4,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    sP2(sK5(sK3),sK3)),
% 0.21/0.49    inference(superposition,[],[f68,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sK3 = k1_tarski(sK5(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f44])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    sK3 = k1_tarski(sK5(sK3)) | v1_xboole_0(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK3),sK3)),
% 0.21/0.49    inference(resolution,[],[f80,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK5(X0),X0) | ~sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK5(X0)) = X0 & m1_subset_1(sK5(X0),X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK5(X0)) = X0 & m1_subset_1(sK5(X0),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(rectify,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (sP0(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    sP0(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v1_zfmisc_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    sP0(sK3) | ~v1_zfmisc_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f74,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | ~v1_zfmisc_1(X0) | ~sP1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (((v1_zfmisc_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_zfmisc_1(X0))) | ~sP1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  % (32486)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    sP1(sK3)),
% 0.21/0.49    inference(resolution,[],[f44,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (sP1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (sP1(X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(definition_folding,[],[f14,f25,f24])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    sK3 = k1_tarski(sK5(sK3)) | ~m1_subset_1(sK5(sK3),sK3) | v1_xboole_0(sK3)),
% 0.21/0.49    inference(superposition,[],[f82,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    sK3 = k6_domain_1(sK3,sK5(sK3))),
% 0.21/0.49    inference(resolution,[],[f80,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (k6_domain_1(X0,sK5(X0)) = X0 | ~sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (sP2(X0,k1_tarski(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP2(X0,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_tarski(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP2(X0,X1))),
% 0.21/0.49    inference(definition_folding,[],[f1,f27])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~sP2(sK4,sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f108,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    sK3 = sK6(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f194,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : (~v1_subset_1(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    sK3 = sK6(sK3) | ~m1_subset_1(sK6(sK3),k1_zfmisc_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f168,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ~r1_tarski(sK6(sK3),sK3) | sK3 = sK6(sK3)),
% 0.21/0.49    inference(resolution,[],[f161,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,sK3) | sK3 = X0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f44])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (sK3 = X0 | ~r1_tarski(X0,sK3) | v1_xboole_0(sK3) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f47,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~v1_xboole_0(sK6(sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f160,f56])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~v1_xboole_0(sK6(sK3)) | ~m1_subset_1(sK6(sK3),k1_zfmisc_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f73,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_subset_1(sK6(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X4] : (v1_subset_1(X4,sK3) | ~v1_xboole_0(X4) | ~m1_subset_1(X4,k1_zfmisc_1(sK3))) )),
% 0.21/0.49    inference(resolution,[],[f44,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ~sP2(sK4,sK6(sK3))),
% 0.21/0.49    inference(resolution,[],[f93,f57])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0] : (v1_subset_1(X0,sK3) | ~sP2(sK4,X0)) )),
% 0.21/0.49    inference(superposition,[],[f92,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tarski(X0) = X1 | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    v1_subset_1(k1_tarski(sK4),sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f44])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    v1_subset_1(k1_tarski(sK4),sK3) | v1_xboole_0(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f45])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    v1_subset_1(k1_tarski(sK4),sK3) | ~m1_subset_1(sK4,sK3) | v1_xboole_0(sK3)),
% 0.21/0.49    inference(superposition,[],[f46,f59])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v1_subset_1(k6_domain_1(sK3,sK4),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (32478)------------------------------
% 0.21/0.49  % (32478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32478)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (32478)Memory used [KB]: 1663
% 0.21/0.49  % (32478)Time elapsed: 0.075 s
% 0.21/0.49  % (32478)------------------------------
% 0.21/0.49  % (32478)------------------------------
% 0.21/0.50  % (32469)Success in time 0.135 s
%------------------------------------------------------------------------------
