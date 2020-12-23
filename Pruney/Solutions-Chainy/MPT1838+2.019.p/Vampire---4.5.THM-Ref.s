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
% DateTime   : Thu Dec  3 13:19:56 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  116 (3352 expanded)
%              Number of leaves         :   19 ( 966 expanded)
%              Depth                    :   27
%              Number of atoms          :  333 (14904 expanded)
%              Number of equality atoms :  111 (3968 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(subsumption_resolution,[],[f242,f195])).

fof(f195,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f194])).

fof(f194,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f180,f193])).

fof(f193,plain,(
    ~ r2_hidden(k3_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f191,f98])).

fof(f98,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f96,f49])).

fof(f49,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f96,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f191,plain,
    ( ~ r2_hidden(k3_tarski(sK1),sK0)
    | r1_tarski(sK1,sK0) ),
    inference(superposition,[],[f67,f184])).

fof(f184,plain,(
    k3_tarski(sK1) = sK4(sK1,sK0) ),
    inference(resolution,[],[f137,f98])).

fof(f137,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | k3_tarski(sK1) = sK4(sK1,X2) ) ),
    inference(forward_demodulation,[],[f127,f126])).

fof(f126,plain,(
    sK2(sK1) = k3_tarski(sK1) ),
    inference(superposition,[],[f90,f118])).

fof(f118,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f117,f105])).

fof(f105,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f104,f46])).

fof(f46,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f53,f47])).

fof(f47,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f117,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f116,f46])).

fof(f116,plain,
    ( v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(resolution,[],[f110,f47])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f109])).

% (15475)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (15488)Refutation not found, incomplete strategy% (15488)------------------------------
% (15488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15488)Termination reason: Refutation not found, incomplete strategy

% (15488)Memory used [KB]: 10618
% (15488)Time elapsed: 0.117 s
% (15488)------------------------------
% (15488)------------------------------
% (15472)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (15471)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (15490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (15471)Refutation not found, incomplete strategy% (15471)------------------------------
% (15471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15471)Termination reason: Refutation not found, incomplete strategy

% (15471)Memory used [KB]: 1663
% (15471)Time elapsed: 0.141 s
% (15471)------------------------------
% (15471)------------------------------
fof(f109,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f90,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(backward_demodulation,[],[f86,f89])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f60,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f86,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f58,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

% (15482)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f127,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | sK2(sK1) = sK4(sK1,X2) ) ),
    inference(superposition,[],[f91,f118])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f66,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
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

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f180,plain,
    ( r2_hidden(k3_tarski(sK1),sK0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( r2_hidden(k3_tarski(sK1),sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f55,f172])).

fof(f172,plain,
    ( k3_tarski(sK1) = sK3(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f167,f55])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k3_tarski(sK1) = X0 ) ),
    inference(resolution,[],[f133,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f65,f48])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k3_tarski(sK1) = X1 ) ),
    inference(backward_demodulation,[],[f121,f126])).

fof(f121,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | sK2(sK1) = X1 ) ),
    inference(superposition,[],[f77,f118])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f242,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f238,f196])).

fof(f196,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f48,f194])).

fof(f238,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f237,f138])).

fof(f138,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k3_tarski(sK1))
      | ~ r1_tarski(X3,sK1)
      | v1_xboole_0(X3) ) ),
    inference(forward_demodulation,[],[f128,f126])).

fof(f128,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | ~ r1_tarski(X3,sK2(sK1))
      | v1_xboole_0(X3) ) ),
    inference(superposition,[],[f112,f118])).

fof(f112,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_tarski(X3))
      | ~ r1_tarski(X2,X3)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f72,f85])).

fof(f85,plain,(
    ! [X0] : r1_xboole_0(X0,k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f83,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f57,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f83,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f56,f82])).

fof(f82,plain,(
    ! [X1] : sK3(k1_tarski(X1)) = X1 ),
    inference(subsumption_resolution,[],[f81,f79])).

fof(f81,plain,(
    ! [X1] :
      ( sK3(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f77,f55])).

fof(f56,plain,(
    ! [X0] :
      ( r1_xboole_0(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f237,plain,(
    r1_tarski(k1_xboole_0,k3_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f236,f206])).

fof(f206,plain,(
    ~ r2_hidden(k3_tarski(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f193,f194])).

fof(f236,plain,
    ( r2_hidden(k3_tarski(sK1),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k3_tarski(sK1)) ),
    inference(superposition,[],[f66,f234])).

fof(f234,plain,(
    k3_tarski(sK1) = sK4(k1_xboole_0,k3_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f233,f195])).

fof(f233,plain,
    ( k3_tarski(sK1) = sK4(k1_xboole_0,k3_tarski(sK1))
    | v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f231,f196])).

fof(f231,plain,
    ( k3_tarski(sK1) = sK4(k1_xboole_0,k3_tarski(sK1))
    | ~ r1_tarski(k1_xboole_0,sK1)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f207,f138])).

% (15482)Refutation not found, incomplete strategy% (15482)------------------------------
% (15482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15482)Termination reason: Refutation not found, incomplete strategy

% (15482)Memory used [KB]: 10618
% (15482)Time elapsed: 0.142 s
% (15482)------------------------------
% (15482)------------------------------
fof(f207,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | k3_tarski(sK1) = sK4(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f203,f194])).

fof(f203,plain,(
    ! [X0] :
      ( k3_tarski(sK1) = sK4(k1_xboole_0,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(backward_demodulation,[],[f173,f194])).

fof(f173,plain,(
    ! [X0] :
      ( k3_tarski(sK1) = sK4(sK0,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f167,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:54:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (797769728)
% 0.13/0.37  ipcrm: permission denied for id (797802497)
% 0.13/0.37  ipcrm: permission denied for id (797835268)
% 0.13/0.37  ipcrm: permission denied for id (797868038)
% 0.13/0.38  ipcrm: permission denied for id (797900808)
% 0.13/0.38  ipcrm: permission denied for id (797933577)
% 0.13/0.38  ipcrm: permission denied for id (797966346)
% 0.13/0.38  ipcrm: permission denied for id (798031884)
% 0.13/0.38  ipcrm: permission denied for id (798097422)
% 0.13/0.39  ipcrm: permission denied for id (798130192)
% 0.13/0.39  ipcrm: permission denied for id (798228500)
% 0.13/0.39  ipcrm: permission denied for id (798261269)
% 0.13/0.39  ipcrm: permission denied for id (798294038)
% 0.13/0.40  ipcrm: permission denied for id (798326807)
% 0.13/0.40  ipcrm: permission denied for id (798359576)
% 0.13/0.40  ipcrm: permission denied for id (798392345)
% 0.13/0.40  ipcrm: permission denied for id (798425114)
% 0.13/0.40  ipcrm: permission denied for id (798457883)
% 0.21/0.42  ipcrm: permission denied for id (798720041)
% 0.21/0.42  ipcrm: permission denied for id (798752810)
% 0.21/0.42  ipcrm: permission denied for id (798785579)
% 0.21/0.42  ipcrm: permission denied for id (798818348)
% 0.21/0.42  ipcrm: permission denied for id (798851117)
% 0.21/0.42  ipcrm: permission denied for id (798883886)
% 0.21/0.43  ipcrm: permission denied for id (798916655)
% 0.21/0.43  ipcrm: permission denied for id (798982193)
% 0.21/0.43  ipcrm: permission denied for id (799047731)
% 0.21/0.43  ipcrm: permission denied for id (799113269)
% 0.21/0.44  ipcrm: permission denied for id (799211576)
% 0.21/0.45  ipcrm: permission denied for id (799473728)
% 0.21/0.46  ipcrm: permission denied for id (799703113)
% 0.21/0.46  ipcrm: permission denied for id (799768651)
% 0.21/0.46  ipcrm: permission denied for id (799834188)
% 0.21/0.46  ipcrm: permission denied for id (799899726)
% 0.21/0.47  ipcrm: permission denied for id (799998034)
% 0.21/0.47  ipcrm: permission denied for id (800063573)
% 0.21/0.47  ipcrm: permission denied for id (800096342)
% 0.21/0.48  ipcrm: permission denied for id (800129111)
% 0.21/0.48  ipcrm: permission denied for id (800194649)
% 0.21/0.48  ipcrm: permission denied for id (800325725)
% 0.21/0.49  ipcrm: permission denied for id (800391263)
% 0.21/0.49  ipcrm: permission denied for id (800456801)
% 0.21/0.49  ipcrm: permission denied for id (800489570)
% 0.21/0.49  ipcrm: permission denied for id (800555108)
% 0.21/0.49  ipcrm: permission denied for id (800587877)
% 0.21/0.49  ipcrm: permission denied for id (800620646)
% 0.21/0.50  ipcrm: permission denied for id (800653415)
% 0.21/0.50  ipcrm: permission denied for id (800718952)
% 0.21/0.50  ipcrm: permission denied for id (800817259)
% 0.21/0.50  ipcrm: permission denied for id (800850028)
% 0.21/0.50  ipcrm: permission denied for id (800882797)
% 0.21/0.51  ipcrm: permission denied for id (800981104)
% 0.21/0.51  ipcrm: permission denied for id (801144947)
% 0.21/0.51  ipcrm: permission denied for id (801177716)
% 0.21/0.52  ipcrm: permission denied for id (801243256)
% 0.21/0.52  ipcrm: permission denied for id (801276026)
% 0.21/0.52  ipcrm: permission denied for id (801374334)
% 0.84/0.65  % (15483)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.15/0.66  % (15499)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.15/0.67  % (15480)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.15/0.67  % (15480)Refutation not found, incomplete strategy% (15480)------------------------------
% 1.15/0.67  % (15480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.67  % (15480)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.67  
% 1.15/0.67  % (15480)Memory used [KB]: 10618
% 1.15/0.67  % (15480)Time elapsed: 0.088 s
% 1.15/0.67  % (15480)------------------------------
% 1.15/0.67  % (15480)------------------------------
% 1.15/0.67  % (15493)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.15/0.67  % (15489)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.15/0.68  % (15485)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.15/0.68  % (15497)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.15/0.68  % (15493)Refutation not found, incomplete strategy% (15493)------------------------------
% 1.15/0.68  % (15493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.68  % (15493)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.68  
% 1.15/0.68  % (15493)Memory used [KB]: 10746
% 1.15/0.68  % (15493)Time elapsed: 0.105 s
% 1.15/0.68  % (15493)------------------------------
% 1.15/0.68  % (15493)------------------------------
% 1.15/0.69  % (15479)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.15/0.69  % (15488)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.15/0.70  % (15496)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.15/0.70  % (15478)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.15/0.71  % (15478)Refutation found. Thanks to Tanya!
% 1.15/0.71  % SZS status Theorem for theBenchmark
% 1.15/0.71  % SZS output start Proof for theBenchmark
% 1.15/0.71  fof(f243,plain,(
% 1.15/0.71    $false),
% 1.15/0.71    inference(subsumption_resolution,[],[f242,f195])).
% 1.15/0.71  fof(f195,plain,(
% 1.15/0.71    ~v1_xboole_0(k1_xboole_0)),
% 1.15/0.71    inference(backward_demodulation,[],[f45,f194])).
% 1.15/0.71  fof(f194,plain,(
% 1.15/0.71    k1_xboole_0 = sK0),
% 1.15/0.71    inference(subsumption_resolution,[],[f180,f193])).
% 1.15/0.71  fof(f193,plain,(
% 1.15/0.71    ~r2_hidden(k3_tarski(sK1),sK0)),
% 1.15/0.71    inference(subsumption_resolution,[],[f191,f98])).
% 1.15/0.71  fof(f98,plain,(
% 1.15/0.71    ~r1_tarski(sK1,sK0)),
% 1.15/0.71    inference(subsumption_resolution,[],[f96,f49])).
% 1.15/0.71  fof(f49,plain,(
% 1.15/0.71    sK0 != sK1),
% 1.15/0.71    inference(cnf_transformation,[],[f28])).
% 1.15/0.71  fof(f28,plain,(
% 1.15/0.71    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.15/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27,f26])).
% 1.15/0.71  fof(f26,plain,(
% 1.15/0.71    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.15/0.71    introduced(choice_axiom,[])).
% 1.15/0.71  fof(f27,plain,(
% 1.15/0.71    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 1.15/0.71    introduced(choice_axiom,[])).
% 1.15/0.71  fof(f17,plain,(
% 1.15/0.71    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.15/0.71    inference(flattening,[],[f16])).
% 1.15/0.71  fof(f16,plain,(
% 1.15/0.71    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.15/0.71    inference(ennf_transformation,[],[f15])).
% 1.15/0.71  fof(f15,negated_conjecture,(
% 1.15/0.71    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.15/0.71    inference(negated_conjecture,[],[f14])).
% 1.15/0.71  fof(f14,conjecture,(
% 1.15/0.71    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.15/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.15/0.71  fof(f96,plain,(
% 1.15/0.71    ~r1_tarski(sK1,sK0) | sK0 = sK1),
% 1.15/0.71    inference(resolution,[],[f64,f48])).
% 1.15/0.71  fof(f48,plain,(
% 1.15/0.71    r1_tarski(sK0,sK1)),
% 1.15/0.71    inference(cnf_transformation,[],[f28])).
% 1.15/0.71  fof(f64,plain,(
% 1.15/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.15/0.71    inference(cnf_transformation,[],[f36])).
% 1.15/0.71  fof(f36,plain,(
% 1.15/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.15/0.71    inference(flattening,[],[f35])).
% 1.15/0.71  fof(f35,plain,(
% 1.15/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.15/0.71    inference(nnf_transformation,[],[f2])).
% 1.15/0.71  fof(f2,axiom,(
% 1.15/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.15/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.15/0.71  fof(f191,plain,(
% 1.15/0.71    ~r2_hidden(k3_tarski(sK1),sK0) | r1_tarski(sK1,sK0)),
% 1.15/0.71    inference(superposition,[],[f67,f184])).
% 1.15/0.71  fof(f184,plain,(
% 1.15/0.71    k3_tarski(sK1) = sK4(sK1,sK0)),
% 1.15/0.71    inference(resolution,[],[f137,f98])).
% 1.15/0.71  fof(f137,plain,(
% 1.15/0.71    ( ! [X2] : (r1_tarski(sK1,X2) | k3_tarski(sK1) = sK4(sK1,X2)) )),
% 1.15/0.71    inference(forward_demodulation,[],[f127,f126])).
% 1.15/0.71  fof(f126,plain,(
% 1.15/0.71    sK2(sK1) = k3_tarski(sK1)),
% 1.15/0.71    inference(superposition,[],[f90,f118])).
% 1.15/0.71  fof(f118,plain,(
% 1.15/0.71    sK1 = k1_tarski(sK2(sK1))),
% 1.15/0.71    inference(forward_demodulation,[],[f117,f105])).
% 1.15/0.71  fof(f105,plain,(
% 1.15/0.71    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 1.15/0.71    inference(subsumption_resolution,[],[f104,f46])).
% 1.15/0.71  fof(f46,plain,(
% 1.15/0.71    ~v1_xboole_0(sK1)),
% 1.15/0.71    inference(cnf_transformation,[],[f28])).
% 1.15/0.71  fof(f104,plain,(
% 1.15/0.71    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 1.15/0.71    inference(resolution,[],[f53,f47])).
% 1.15/0.71  fof(f47,plain,(
% 1.15/0.71    v1_zfmisc_1(sK1)),
% 1.15/0.71    inference(cnf_transformation,[],[f28])).
% 1.15/0.71  fof(f53,plain,(
% 1.15/0.71    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 1.15/0.71    inference(cnf_transformation,[],[f32])).
% 1.15/0.71  fof(f32,plain,(
% 1.15/0.71    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.15/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.15/0.71  fof(f31,plain,(
% 1.15/0.71    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 1.15/0.71    introduced(choice_axiom,[])).
% 1.15/0.71  fof(f30,plain,(
% 1.15/0.71    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.15/0.71    inference(rectify,[],[f29])).
% 1.15/0.71  fof(f29,plain,(
% 1.15/0.71    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.15/0.71    inference(nnf_transformation,[],[f18])).
% 1.15/0.71  fof(f18,plain,(
% 1.15/0.71    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.15/0.71    inference(ennf_transformation,[],[f13])).
% 1.15/0.71  fof(f13,axiom,(
% 1.15/0.71    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.15/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.15/0.71  fof(f117,plain,(
% 1.15/0.71    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 1.15/0.71    inference(subsumption_resolution,[],[f116,f46])).
% 1.15/0.71  fof(f116,plain,(
% 1.15/0.71    v1_xboole_0(sK1) | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 1.15/0.71    inference(resolution,[],[f110,f47])).
% 1.15/0.71  fof(f110,plain,(
% 1.15/0.71    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))) )),
% 1.15/0.71    inference(duplicate_literal_removal,[],[f109])).
% 1.15/0.71  % (15475)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.15/0.71  % (15488)Refutation not found, incomplete strategy% (15488)------------------------------
% 1.15/0.71  % (15488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.71  % (15488)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.71  
% 1.15/0.71  % (15488)Memory used [KB]: 10618
% 1.15/0.71  % (15488)Time elapsed: 0.117 s
% 1.15/0.71  % (15488)------------------------------
% 1.15/0.71  % (15488)------------------------------
% 1.15/0.72  % (15472)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.15/0.72  % (15471)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.15/0.72  % (15490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.15/0.72  % (15471)Refutation not found, incomplete strategy% (15471)------------------------------
% 1.15/0.72  % (15471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.72  % (15471)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.72  
% 1.15/0.72  % (15471)Memory used [KB]: 1663
% 1.15/0.72  % (15471)Time elapsed: 0.141 s
% 1.15/0.72  % (15471)------------------------------
% 1.15/0.72  % (15471)------------------------------
% 1.15/0.72  fof(f109,plain,(
% 1.15/0.72    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.15/0.72    inference(resolution,[],[f61,f52])).
% 1.15/0.72  fof(f52,plain,(
% 1.15/0.72    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f32])).
% 1.15/0.72  fof(f61,plain,(
% 1.15/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f22])).
% 1.15/0.72  fof(f22,plain,(
% 1.15/0.72    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.15/0.72    inference(flattening,[],[f21])).
% 1.15/0.72  fof(f21,plain,(
% 1.15/0.72    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.15/0.72    inference(ennf_transformation,[],[f12])).
% 1.15/0.72  fof(f12,axiom,(
% 1.15/0.72    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.15/0.72  fof(f90,plain,(
% 1.15/0.72    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.15/0.72    inference(backward_demodulation,[],[f86,f89])).
% 1.15/0.72  fof(f89,plain,(
% 1.15/0.72    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.15/0.72    inference(resolution,[],[f60,f73])).
% 1.15/0.72  fof(f73,plain,(
% 1.15/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.15/0.72    inference(equality_resolution,[],[f63])).
% 1.15/0.72  fof(f63,plain,(
% 1.15/0.72    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.15/0.72    inference(cnf_transformation,[],[f36])).
% 1.15/0.72  fof(f60,plain,(
% 1.15/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.15/0.72    inference(cnf_transformation,[],[f20])).
% 1.15/0.72  fof(f20,plain,(
% 1.15/0.72    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.15/0.72    inference(ennf_transformation,[],[f3])).
% 1.15/0.72  fof(f3,axiom,(
% 1.15/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.15/0.72  fof(f86,plain,(
% 1.15/0.72    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 1.15/0.72    inference(superposition,[],[f58,f51])).
% 1.15/0.72  fof(f51,plain,(
% 1.15/0.72    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f7])).
% 1.15/0.72  % (15482)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.15/0.72  fof(f7,axiom,(
% 1.15/0.72    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.15/0.72  fof(f58,plain,(
% 1.15/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.15/0.72    inference(cnf_transformation,[],[f9])).
% 1.15/0.72  fof(f9,axiom,(
% 1.15/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.15/0.72  fof(f127,plain,(
% 1.15/0.72    ( ! [X2] : (r1_tarski(sK1,X2) | sK2(sK1) = sK4(sK1,X2)) )),
% 1.15/0.72    inference(superposition,[],[f91,f118])).
% 1.15/0.72  fof(f91,plain,(
% 1.15/0.72    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 1.15/0.72    inference(resolution,[],[f66,f77])).
% 1.15/0.72  fof(f77,plain,(
% 1.15/0.72    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.15/0.72    inference(equality_resolution,[],[f68])).
% 1.15/0.72  fof(f68,plain,(
% 1.15/0.72    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.15/0.72    inference(cnf_transformation,[],[f44])).
% 1.15/0.72  fof(f44,plain,(
% 1.15/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 1.15/0.72  fof(f43,plain,(
% 1.15/0.72    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.15/0.72    introduced(choice_axiom,[])).
% 1.15/0.72  fof(f42,plain,(
% 1.15/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.72    inference(rectify,[],[f41])).
% 1.15/0.72  fof(f41,plain,(
% 1.15/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.72    inference(nnf_transformation,[],[f6])).
% 1.15/0.72  fof(f6,axiom,(
% 1.15/0.72    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.15/0.72  fof(f66,plain,(
% 1.15/0.72    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f40])).
% 1.15/0.72  fof(f40,plain,(
% 1.15/0.72    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.15/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.15/0.72  fof(f39,plain,(
% 1.15/0.72    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.15/0.72    introduced(choice_axiom,[])).
% 1.15/0.72  fof(f38,plain,(
% 1.15/0.72    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.15/0.72    inference(rectify,[],[f37])).
% 1.15/0.72  fof(f37,plain,(
% 1.15/0.72    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.15/0.72    inference(nnf_transformation,[],[f23])).
% 1.15/0.72  fof(f23,plain,(
% 1.15/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.15/0.72    inference(ennf_transformation,[],[f1])).
% 1.15/0.72  fof(f1,axiom,(
% 1.15/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.15/0.72  fof(f67,plain,(
% 1.15/0.72    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f40])).
% 1.15/0.72  fof(f180,plain,(
% 1.15/0.72    r2_hidden(k3_tarski(sK1),sK0) | k1_xboole_0 = sK0),
% 1.15/0.72    inference(duplicate_literal_removal,[],[f179])).
% 1.15/0.72  fof(f179,plain,(
% 1.15/0.72    r2_hidden(k3_tarski(sK1),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.15/0.72    inference(superposition,[],[f55,f172])).
% 1.15/0.72  fof(f172,plain,(
% 1.15/0.72    k3_tarski(sK1) = sK3(sK0) | k1_xboole_0 = sK0),
% 1.15/0.72    inference(resolution,[],[f167,f55])).
% 1.15/0.72  fof(f167,plain,(
% 1.15/0.72    ( ! [X0] : (~r2_hidden(X0,sK0) | k3_tarski(sK1) = X0) )),
% 1.15/0.72    inference(resolution,[],[f133,f99])).
% 1.15/0.72  fof(f99,plain,(
% 1.15/0.72    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.15/0.72    inference(resolution,[],[f65,f48])).
% 1.15/0.72  fof(f65,plain,(
% 1.15/0.72    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f40])).
% 1.15/0.72  fof(f133,plain,(
% 1.15/0.72    ( ! [X1] : (~r2_hidden(X1,sK1) | k3_tarski(sK1) = X1) )),
% 1.15/0.72    inference(backward_demodulation,[],[f121,f126])).
% 1.15/0.72  fof(f121,plain,(
% 1.15/0.72    ( ! [X1] : (~r2_hidden(X1,sK1) | sK2(sK1) = X1) )),
% 1.15/0.72    inference(superposition,[],[f77,f118])).
% 1.15/0.72  fof(f55,plain,(
% 1.15/0.72    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.15/0.72    inference(cnf_transformation,[],[f34])).
% 1.15/0.72  fof(f34,plain,(
% 1.15/0.72    ! [X0] : ((r1_xboole_0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.15/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f33])).
% 1.15/0.72  fof(f33,plain,(
% 1.15/0.72    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) => (r1_xboole_0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 1.15/0.72    introduced(choice_axiom,[])).
% 1.15/0.72  fof(f19,plain,(
% 1.15/0.72    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.15/0.72    inference(ennf_transformation,[],[f11])).
% 1.15/0.72  fof(f11,axiom,(
% 1.15/0.72    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 1.15/0.72  fof(f45,plain,(
% 1.15/0.72    ~v1_xboole_0(sK0)),
% 1.15/0.72    inference(cnf_transformation,[],[f28])).
% 1.15/0.72  fof(f242,plain,(
% 1.15/0.72    v1_xboole_0(k1_xboole_0)),
% 1.15/0.72    inference(subsumption_resolution,[],[f238,f196])).
% 1.15/0.72  fof(f196,plain,(
% 1.15/0.72    r1_tarski(k1_xboole_0,sK1)),
% 1.15/0.72    inference(backward_demodulation,[],[f48,f194])).
% 1.15/0.72  fof(f238,plain,(
% 1.15/0.72    ~r1_tarski(k1_xboole_0,sK1) | v1_xboole_0(k1_xboole_0)),
% 1.15/0.72    inference(resolution,[],[f237,f138])).
% 1.15/0.72  fof(f138,plain,(
% 1.15/0.72    ( ! [X3] : (~r1_tarski(X3,k3_tarski(sK1)) | ~r1_tarski(X3,sK1) | v1_xboole_0(X3)) )),
% 1.15/0.72    inference(forward_demodulation,[],[f128,f126])).
% 1.15/0.72  fof(f128,plain,(
% 1.15/0.72    ( ! [X3] : (~r1_tarski(X3,sK1) | ~r1_tarski(X3,sK2(sK1)) | v1_xboole_0(X3)) )),
% 1.15/0.72    inference(superposition,[],[f112,f118])).
% 1.15/0.72  fof(f112,plain,(
% 1.15/0.72    ( ! [X2,X3] : (~r1_tarski(X2,k1_tarski(X3)) | ~r1_tarski(X2,X3) | v1_xboole_0(X2)) )),
% 1.15/0.72    inference(resolution,[],[f72,f85])).
% 1.15/0.72  fof(f85,plain,(
% 1.15/0.72    ( ! [X0] : (r1_xboole_0(X0,k1_tarski(X0))) )),
% 1.15/0.72    inference(subsumption_resolution,[],[f83,f79])).
% 1.15/0.72  fof(f79,plain,(
% 1.15/0.72    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 1.15/0.72    inference(superposition,[],[f57,f50])).
% 1.15/0.72  fof(f50,plain,(
% 1.15/0.72    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.15/0.72    inference(cnf_transformation,[],[f4])).
% 1.15/0.72  fof(f4,axiom,(
% 1.15/0.72    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.15/0.72  fof(f57,plain,(
% 1.15/0.72    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f10])).
% 1.15/0.72  fof(f10,axiom,(
% 1.15/0.72    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.15/0.72  fof(f83,plain,(
% 1.15/0.72    ( ! [X0] : (r1_xboole_0(X0,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.15/0.72    inference(superposition,[],[f56,f82])).
% 1.15/0.72  fof(f82,plain,(
% 1.15/0.72    ( ! [X1] : (sK3(k1_tarski(X1)) = X1) )),
% 1.15/0.72    inference(subsumption_resolution,[],[f81,f79])).
% 1.15/0.72  fof(f81,plain,(
% 1.15/0.72    ( ! [X1] : (sK3(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 1.15/0.72    inference(resolution,[],[f77,f55])).
% 1.15/0.72  fof(f56,plain,(
% 1.15/0.72    ( ! [X0] : (r1_xboole_0(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.15/0.72    inference(cnf_transformation,[],[f34])).
% 1.15/0.72  fof(f72,plain,(
% 1.15/0.72    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 1.15/0.72    inference(cnf_transformation,[],[f25])).
% 1.15/0.72  fof(f25,plain,(
% 1.15/0.72    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 1.15/0.72    inference(flattening,[],[f24])).
% 1.15/0.72  fof(f24,plain,(
% 1.15/0.72    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 1.15/0.72    inference(ennf_transformation,[],[f5])).
% 1.15/0.72  fof(f5,axiom,(
% 1.15/0.72    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 1.15/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 1.15/0.72  fof(f237,plain,(
% 1.15/0.72    r1_tarski(k1_xboole_0,k3_tarski(sK1))),
% 1.15/0.72    inference(subsumption_resolution,[],[f236,f206])).
% 1.15/0.72  fof(f206,plain,(
% 1.15/0.72    ~r2_hidden(k3_tarski(sK1),k1_xboole_0)),
% 1.15/0.72    inference(backward_demodulation,[],[f193,f194])).
% 1.15/0.72  fof(f236,plain,(
% 1.15/0.72    r2_hidden(k3_tarski(sK1),k1_xboole_0) | r1_tarski(k1_xboole_0,k3_tarski(sK1))),
% 1.15/0.72    inference(superposition,[],[f66,f234])).
% 1.15/0.72  fof(f234,plain,(
% 1.15/0.72    k3_tarski(sK1) = sK4(k1_xboole_0,k3_tarski(sK1))),
% 1.15/0.72    inference(subsumption_resolution,[],[f233,f195])).
% 1.15/0.72  fof(f233,plain,(
% 1.15/0.72    k3_tarski(sK1) = sK4(k1_xboole_0,k3_tarski(sK1)) | v1_xboole_0(k1_xboole_0)),
% 1.15/0.72    inference(subsumption_resolution,[],[f231,f196])).
% 1.15/0.72  fof(f231,plain,(
% 1.15/0.72    k3_tarski(sK1) = sK4(k1_xboole_0,k3_tarski(sK1)) | ~r1_tarski(k1_xboole_0,sK1) | v1_xboole_0(k1_xboole_0)),
% 1.15/0.72    inference(resolution,[],[f207,f138])).
% 1.15/0.72  % (15482)Refutation not found, incomplete strategy% (15482)------------------------------
% 1.15/0.72  % (15482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.72  % (15482)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.72  
% 1.15/0.72  % (15482)Memory used [KB]: 10618
% 1.15/0.72  % (15482)Time elapsed: 0.142 s
% 1.15/0.72  % (15482)------------------------------
% 1.15/0.72  % (15482)------------------------------
% 1.15/0.72  fof(f207,plain,(
% 1.15/0.72    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | k3_tarski(sK1) = sK4(k1_xboole_0,X0)) )),
% 1.15/0.72    inference(forward_demodulation,[],[f203,f194])).
% 1.15/0.72  fof(f203,plain,(
% 1.15/0.72    ( ! [X0] : (k3_tarski(sK1) = sK4(k1_xboole_0,X0) | r1_tarski(sK0,X0)) )),
% 1.15/0.72    inference(backward_demodulation,[],[f173,f194])).
% 1.15/0.72  fof(f173,plain,(
% 1.15/0.72    ( ! [X0] : (k3_tarski(sK1) = sK4(sK0,X0) | r1_tarski(sK0,X0)) )),
% 1.15/0.72    inference(resolution,[],[f167,f66])).
% 1.15/0.72  % SZS output end Proof for theBenchmark
% 1.15/0.72  % (15478)------------------------------
% 1.15/0.72  % (15478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.72  % (15478)Termination reason: Refutation
% 1.15/0.72  
% 1.15/0.72  % (15478)Memory used [KB]: 6396
% 1.15/0.72  % (15478)Time elapsed: 0.111 s
% 1.15/0.72  % (15478)------------------------------
% 1.15/0.72  % (15478)------------------------------
% 1.15/0.73  % (15316)Success in time 0.359 s
%------------------------------------------------------------------------------
