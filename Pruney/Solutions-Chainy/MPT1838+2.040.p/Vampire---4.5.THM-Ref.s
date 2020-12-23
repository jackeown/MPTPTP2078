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
% DateTime   : Thu Dec  3 13:19:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 117 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 483 expanded)
%              Number of equality atoms :   90 ( 158 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f76,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f31,f73])).

fof(f73,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f71,f66])).

fof(f66,plain,(
    sK2 = k1_tarski(sK3(sK2)) ),
    inference(forward_demodulation,[],[f65,f61])).

fof(f61,plain,(
    sK2 = k6_domain_1(sK2,sK3(sK2)) ),
    inference(subsumption_resolution,[],[f60,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != sK2
    & r1_tarski(sK1,sK2)
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK1 != X1
          & r1_tarski(sK1,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( sK1 != X1
        & r1_tarski(sK1,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK1 != sK2
      & r1_tarski(sK1,sK2)
      & v1_zfmisc_1(sK2)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f60,plain,
    ( sK2 = k6_domain_1(sK2,sK3(sK2))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK3(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f65,plain,(
    k6_domain_1(sK2,sK3(sK2)) = k1_tarski(sK3(sK2)) ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f64,plain,
    ( v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK3(sK2)) = k1_tarski(sK3(sK2)) ),
    inference(resolution,[],[f63,f33])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f71,plain,(
    ! [X2] :
      ( sK2 != k1_tarski(X2)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f70,f35])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X2] :
      ( sK2 != k1_tarski(X2)
      | sK1 = sK2
      | k1_xboole_0 = sK1 ) ),
    inference(inner_rewriting,[],[f69])).

fof(f69,plain,(
    ! [X2] :
      ( sK2 != k1_tarski(X2)
      | sK1 = k1_tarski(X2)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f52,f59])).

fof(f59,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f57,f58])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f56,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f43,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f57,plain,(
    k2_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f43,f55])).

fof(f55,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = X0
        & k1_tarski(X1) = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (12813)Termination reason: Refutation not found, incomplete strategy
fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | sP0(X2,X0,X1)
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

% (12813)Memory used [KB]: 6140
fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | sP0(X2,X0,X1)
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(definition_folding,[],[f19,f20])).

% (12813)Time elapsed: 0.004 s
% (12813)------------------------------
% (12813)------------------------------
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (12805)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.48  % (12813)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.48  % (12805)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (12813)Refutation not found, incomplete strategy% (12813)------------------------------
% 0.22/0.48  % (12813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f76,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(backward_demodulation,[],[f31,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    k1_xboole_0 = sK1),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    sK2 != sK2 | k1_xboole_0 = sK1),
% 0.22/0.48    inference(superposition,[],[f71,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    sK2 = k1_tarski(sK3(sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f65,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    sK2 = k6_domain_1(sK2,sK3(sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f60,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~v1_xboole_0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    (sK1 != sK2 & r1_tarski(sK1,sK2) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK1 != X1 & r1_tarski(sK1,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X1] : (sK1 != X1 & r1_tarski(sK1,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK1 != sK2 & r1_tarski(sK1,sK2) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    sK2 = k6_domain_1(sK2,sK3(sK2)) | v1_xboole_0(sK2)),
% 0.22/0.49    inference(resolution,[],[f40,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    v1_zfmisc_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK3(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(rectify,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    k6_domain_1(sK2,sK3(sK2)) = k1_tarski(sK3(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f64,f32])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    v1_xboole_0(sK2) | k6_domain_1(sK2,sK3(sK2)) = k1_tarski(sK3(sK2))),
% 0.22/0.49    inference(resolution,[],[f63,f33])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0] : (k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(resolution,[],[f44,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X2] : (sK2 != k1_tarski(X2) | k1_xboole_0 = sK1) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f70,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    sK1 != sK2),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X2] : (sK2 != k1_tarski(X2) | sK1 = sK2 | k1_xboole_0 = sK1) )),
% 0.22/0.49    inference(inner_rewriting,[],[f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X2] : (sK2 != k1_tarski(X2) | sK1 = k1_tarski(X2) | k1_xboole_0 = sK1) )),
% 0.22/0.49    inference(superposition,[],[f52,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    sK2 = k2_xboole_0(sK2,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f57,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(forward_demodulation,[],[f56,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(superposition,[],[f43,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    k2_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0)),
% 0.22/0.49    inference(superposition,[],[f43,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.22/0.49    inference(resolution,[],[f45,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    r1_tarski(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f51,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_tarski(X1) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_tarski(X1) = X0 & k1_tarski(X1) = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.49    inference(rectify,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X2,X0,X1] : ((k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | ~sP0(X2,X0,X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X2,X0,X1] : ((k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | ~sP0(X2,X0,X1))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  % (12813)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | sP0(X2,X0,X1) | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  
% 0.22/0.49  % (12813)Memory used [KB]: 6140
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | sP0(X2,X0,X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.22/0.49    inference(definition_folding,[],[f19,f20])).
% 0.22/0.49  % (12813)Time elapsed: 0.004 s
% 0.22/0.49  % (12813)------------------------------
% 0.22/0.49  % (12813)------------------------------
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ~v1_xboole_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (12805)------------------------------
% 0.22/0.49  % (12805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12805)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (12805)Memory used [KB]: 6268
% 0.22/0.49  % (12805)Time elapsed: 0.066 s
% 0.22/0.49  % (12805)------------------------------
% 0.22/0.49  % (12805)------------------------------
% 0.22/0.49  % (12797)Success in time 0.128 s
%------------------------------------------------------------------------------
