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
% DateTime   : Thu Dec  3 13:20:11 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   45 (  84 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 292 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(resolution,[],[f51,f23])).

fof(f23,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f51,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f40,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f29,f26])).

fof(f26,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f50,plain,(
    ~ v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(superposition,[],[f38,f48])).

fof(f48,plain,(
    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f46,f23])).

fof(f46,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f37,f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X1,X2)) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X2,X0,X1] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n011.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 14:18:56 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.35  % (3139)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.11/0.36  % (3139)Refutation not found, incomplete strategy% (3139)------------------------------
% 0.11/0.36  % (3139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.36  % (3139)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.36  
% 0.11/0.36  % (3139)Memory used [KB]: 10618
% 0.11/0.36  % (3139)Time elapsed: 0.006 s
% 0.11/0.36  % (3139)------------------------------
% 0.11/0.36  % (3139)------------------------------
% 0.11/0.37  % (3129)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.11/0.37  % (3138)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.11/0.37  % (3129)Refutation found. Thanks to Tanya!
% 0.11/0.37  % SZS status Theorem for theBenchmark
% 0.11/0.37  % SZS output start Proof for theBenchmark
% 0.11/0.37  fof(f52,plain,(
% 0.11/0.37    $false),
% 0.11/0.37    inference(resolution,[],[f51,f23])).
% 0.11/0.37  fof(f23,plain,(
% 0.11/0.37    ~v1_xboole_0(sK0)),
% 0.11/0.37    inference(cnf_transformation,[],[f22])).
% 0.11/0.37  fof(f22,plain,(
% 0.11/0.37    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.11/0.37    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).
% 0.11/0.37  fof(f20,plain,(
% 0.11/0.37    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.11/0.37    introduced(choice_axiom,[])).
% 0.11/0.37  fof(f21,plain,(
% 0.11/0.37    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.11/0.37    introduced(choice_axiom,[])).
% 0.11/0.37  fof(f12,plain,(
% 0.11/0.37    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.11/0.37    inference(flattening,[],[f11])).
% 0.11/0.37  fof(f11,plain,(
% 0.11/0.37    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.11/0.37    inference(ennf_transformation,[],[f10])).
% 0.11/0.37  fof(f10,negated_conjecture,(
% 0.11/0.37    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.11/0.37    inference(negated_conjecture,[],[f9])).
% 0.11/0.37  fof(f9,conjecture,(
% 0.11/0.37    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.11/0.37  fof(f51,plain,(
% 0.11/0.37    v1_xboole_0(sK0)),
% 0.11/0.37    inference(resolution,[],[f50,f43])).
% 0.11/0.37  fof(f43,plain,(
% 0.11/0.37    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 0.11/0.37    inference(resolution,[],[f42,f24])).
% 0.11/0.37  fof(f24,plain,(
% 0.11/0.37    m1_subset_1(sK1,sK0)),
% 0.11/0.37    inference(cnf_transformation,[],[f22])).
% 0.11/0.37  fof(f42,plain,(
% 0.11/0.37    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.11/0.37    inference(duplicate_literal_removal,[],[f41])).
% 0.11/0.37  fof(f41,plain,(
% 0.11/0.37    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.11/0.37    inference(resolution,[],[f40,f32])).
% 0.11/0.37  fof(f32,plain,(
% 0.11/0.37    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f19])).
% 0.11/0.37  fof(f19,plain,(
% 0.11/0.37    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.11/0.37    inference(flattening,[],[f18])).
% 0.11/0.37  fof(f18,plain,(
% 0.11/0.37    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.11/0.37    inference(ennf_transformation,[],[f6])).
% 0.11/0.37  fof(f6,axiom,(
% 0.11/0.37    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.11/0.37  fof(f40,plain,(
% 0.11/0.37    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 0.11/0.37    inference(resolution,[],[f39,f25])).
% 0.11/0.37  fof(f25,plain,(
% 0.11/0.37    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.11/0.37    inference(cnf_transformation,[],[f22])).
% 0.11/0.37  fof(f39,plain,(
% 0.11/0.37    ( ! [X0] : (~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | v1_xboole_0(sK0)) )),
% 0.11/0.37    inference(resolution,[],[f29,f26])).
% 0.11/0.37  fof(f26,plain,(
% 0.11/0.37    v1_zfmisc_1(sK0)),
% 0.11/0.37    inference(cnf_transformation,[],[f22])).
% 0.11/0.37  fof(f29,plain,(
% 0.11/0.37    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f15])).
% 0.11/0.37  fof(f15,plain,(
% 0.11/0.37    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.11/0.37    inference(flattening,[],[f14])).
% 0.11/0.37  fof(f14,plain,(
% 0.11/0.37    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.11/0.37    inference(ennf_transformation,[],[f8])).
% 0.11/0.37  fof(f8,axiom,(
% 0.11/0.37    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.11/0.37  fof(f50,plain,(
% 0.11/0.37    ~v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.11/0.37    inference(superposition,[],[f38,f48])).
% 0.11/0.37  fof(f48,plain,(
% 0.11/0.37    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.11/0.37    inference(resolution,[],[f46,f23])).
% 0.11/0.37  fof(f46,plain,(
% 0.11/0.37    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.11/0.37    inference(resolution,[],[f37,f24])).
% 0.11/0.37  fof(f37,plain,(
% 0.11/0.37    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.11/0.37    inference(definition_unfolding,[],[f31,f36])).
% 0.11/0.37  fof(f36,plain,(
% 0.11/0.37    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.11/0.37    inference(definition_unfolding,[],[f27,f35])).
% 0.11/0.37  fof(f35,plain,(
% 0.11/0.37    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.11/0.37    inference(definition_unfolding,[],[f30,f34])).
% 0.11/0.37  fof(f34,plain,(
% 0.11/0.37    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f3])).
% 0.11/0.37  fof(f3,axiom,(
% 0.11/0.37    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.11/0.37  fof(f30,plain,(
% 0.11/0.37    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f2])).
% 0.11/0.37  fof(f2,axiom,(
% 0.11/0.37    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.11/0.37  fof(f27,plain,(
% 0.11/0.37    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f1])).
% 0.11/0.37  fof(f1,axiom,(
% 0.11/0.37    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.11/0.37  fof(f31,plain,(
% 0.11/0.37    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f17])).
% 0.11/0.37  fof(f17,plain,(
% 0.11/0.37    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.11/0.37    inference(flattening,[],[f16])).
% 0.11/0.37  fof(f16,plain,(
% 0.11/0.37    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.11/0.37    inference(ennf_transformation,[],[f7])).
% 0.11/0.37  fof(f7,axiom,(
% 0.11/0.37    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.11/0.37  fof(f38,plain,(
% 0.11/0.37    ( ! [X2,X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X1,X2))) )),
% 0.11/0.37    inference(definition_unfolding,[],[f33,f34])).
% 0.11/0.37  fof(f33,plain,(
% 0.11/0.37    ( ! [X2,X0,X1] : (~v1_xboole_0(k1_enumset1(X0,X1,X2))) )),
% 0.11/0.37    inference(cnf_transformation,[],[f4])).
% 0.11/0.37  fof(f4,axiom,(
% 0.11/0.37    ! [X0,X1,X2] : ~v1_xboole_0(k1_enumset1(X0,X1,X2))),
% 0.11/0.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_subset_1)).
% 0.11/0.37  % SZS output end Proof for theBenchmark
% 0.11/0.37  % (3129)------------------------------
% 0.11/0.37  % (3129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.37  % (3129)Termination reason: Refutation
% 0.11/0.37  
% 0.11/0.37  % (3129)Memory used [KB]: 1663
% 0.11/0.37  % (3129)Time elapsed: 0.047 s
% 0.11/0.37  % (3129)------------------------------
% 0.11/0.37  % (3129)------------------------------
% 0.11/0.37  % (3127)Success in time 0.104 s
%------------------------------------------------------------------------------
