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
% DateTime   : Thu Dec  3 12:50:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 174 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  236 ( 572 expanded)
%              Number of equality atoms :   46 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f128])).

fof(f128,plain,(
    v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f127,f37])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( k1_xboole_0 != sK1
        & r2_hidden(sK1,k2_relat_1(sK0)) )
      | ~ v3_relat_1(sK0) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK0)) )
      | v3_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK0)) )
        | ~ v3_relat_1(sK0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
        | v3_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & r2_hidden(X1,k2_relat_1(sK0)) )
   => ( k1_xboole_0 != sK1
      & r2_hidden(sK1,k2_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f127,plain,
    ( v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f126,f72])).

fof(f72,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f71,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r2_hidden(X0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f51,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f46,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f126,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v3_relat_1(sK0)
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f115,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))
      | v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f65,f64])).

fof(f64,plain,(
    k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (1895)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f41,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f65,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f49,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

fof(f115,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(sK0),X2)
      | ~ r2_hidden(k1_xboole_0,X2)
      | v3_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_xboole_0,X2)
      | r1_tarski(k2_relat_1(sK0),X2)
      | v3_relat_1(sK0)
      | r1_tarski(k2_relat_1(sK0),X2) ) ),
    inference(superposition,[],[f58,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2(k2_relat_1(sK0),X0)
      | v3_relat_1(sK0)
      | r1_tarski(k2_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f38,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK0))
      | k1_xboole_0 = X2
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    ~ v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f117,plain,
    ( ~ v3_relat_1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f109,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ v3_relat_1(sK0) ),
    inference(resolution,[],[f100,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f52,f45])).

fof(f45,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f100,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ v3_relat_1(sK0)
    | ~ v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f82,f90])).

fof(f90,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f66,f64])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r2_hidden(sK1,X0)
      | ~ v3_relat_1(sK0) ) ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (1876)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (1893)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (1899)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (1899)Refutation not found, incomplete strategy% (1899)------------------------------
% 0.21/0.53  % (1899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1893)Refutation not found, incomplete strategy% (1893)------------------------------
% 0.21/0.53  % (1893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1899)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1899)Memory used [KB]: 10746
% 0.21/0.53  % (1899)Time elapsed: 0.109 s
% 0.21/0.53  % (1899)------------------------------
% 0.21/0.53  % (1899)------------------------------
% 0.21/0.53  % (1893)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1893)Memory used [KB]: 1663
% 0.21/0.53  % (1893)Time elapsed: 0.106 s
% 0.21/0.53  % (1893)------------------------------
% 0.21/0.53  % (1893)------------------------------
% 0.21/0.54  % (1878)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (1875)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (1897)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (1874)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (1872)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1873)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1883)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (1871)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (1886)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (1890)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (1880)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (1889)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (1902)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (1892)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (1887)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (1889)Refutation not found, incomplete strategy% (1889)------------------------------
% 0.21/0.55  % (1889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1889)Memory used [KB]: 10618
% 0.21/0.55  % (1889)Time elapsed: 0.139 s
% 0.21/0.55  % (1889)------------------------------
% 0.21/0.55  % (1889)------------------------------
% 0.21/0.55  % (1902)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f119,f128])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    v3_relat_1(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f127,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    v1_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ((k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0)) => ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) => (k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.55    inference(rectify,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ? [X0] : (((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f16])).
% 0.21/0.55  fof(f16,conjecture,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f126,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f71,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(resolution,[],[f51,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f46,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(sK0) | v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.55    inference(resolution,[],[f115,f87])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f65,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(definition_unfolding,[],[f41,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f47,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f50,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f59,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  % (1895)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f49,f63])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (((v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) & (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ( ! [X2] : (r1_tarski(k2_relat_1(sK0),X2) | ~r2_hidden(k1_xboole_0,X2) | v3_relat_1(sK0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(k1_xboole_0,X2) | r1_tarski(k2_relat_1(sK0),X2) | v3_relat_1(sK0) | r1_tarski(k2_relat_1(sK0),X2)) )),
% 0.21/0.55    inference(superposition,[],[f58,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK2(k2_relat_1(sK0),X0) | v3_relat_1(sK0) | r1_tarski(k2_relat_1(sK0),X0)) )),
% 0.21/0.55    inference(resolution,[],[f38,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK0)) | k1_xboole_0 = X2 | v3_relat_1(sK0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    ~v3_relat_1(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f117,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | ~v3_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ~v3_relat_1(sK0) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(resolution,[],[f109,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(resolution,[],[f55,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    r1_tarski(sK1,k1_xboole_0) | ~v3_relat_1(sK0)),
% 0.21/0.55    inference(resolution,[],[f100,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.21/0.55    inference(superposition,[],[f52,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | ~v3_relat_1(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f99,f37])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | ~v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | ~v3_relat_1(sK0) | ~v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.55    inference(resolution,[],[f82,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f66,f64])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f48,f63])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r2_hidden(sK1,X0) | ~v3_relat_1(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f56,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    r2_hidden(sK1,k2_relat_1(sK0)) | ~v3_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (1902)------------------------------
% 0.21/0.55  % (1902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1902)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (1902)Memory used [KB]: 1791
% 0.21/0.55  % (1902)Time elapsed: 0.140 s
% 0.21/0.55  % (1902)------------------------------
% 0.21/0.55  % (1902)------------------------------
% 0.21/0.55  % (1892)Refutation not found, incomplete strategy% (1892)------------------------------
% 0.21/0.55  % (1892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1892)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1892)Memory used [KB]: 10746
% 0.21/0.55  % (1892)Time elapsed: 0.141 s
% 0.21/0.55  % (1892)------------------------------
% 0.21/0.55  % (1892)------------------------------
% 0.21/0.56  % (1870)Success in time 0.185 s
%------------------------------------------------------------------------------
