%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 936 expanded)
%              Number of leaves         :   13 ( 285 expanded)
%              Depth                    :   21
%              Number of atoms          :  181 (3268 expanded)
%              Number of equality atoms :   32 ( 259 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106,f31])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f106,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f100])).

fof(f100,plain,(
    ~ v1_subset_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f41,f88])).

fof(f88,plain,(
    k1_xboole_0 = sK2(sK0) ),
    inference(subsumption_resolution,[],[f86,f71])).

fof(f71,plain,(
    v1_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f51,f69])).

fof(f69,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f42,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f68,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f62,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    r1_tarski(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f54,f50])).

fof(f50,plain,(
    k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f48,f31])).

fof(f48,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f54,plain,(
    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f52,f31])).

fof(f52,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f59,f31])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f38,f34])).

fof(f34,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f51,plain,(
    v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f33,f50])).

fof(f33,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( ~ v1_subset_1(sK0,sK0)
    | k1_xboole_0 = sK2(sK0) ),
    inference(superposition,[],[f41,f66])).

fof(f66,plain,
    ( sK0 = sK2(sK0)
    | k1_xboole_0 = sK2(sK0) ),
    inference(resolution,[],[f61,f39])).

% (6741)Refutation not found, incomplete strategy% (6741)------------------------------
% (6741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f61,plain,
    ( v1_xboole_0(sK2(sK0))
    | sK0 = sK2(sK0) ),
    inference(resolution,[],[f60,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(sK2(X0),X0) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK2(X0),X0)
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f41,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,
    ( v1_subset_1(k1_xboole_0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f40,f88])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f94,f88])).

fof(f94,plain,(
    ! [X0] :
      ( v1_subset_1(k1_xboole_0,X0)
      | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f93,f88])).

fof(f93,plain,(
    ! [X0] :
      ( v1_subset_1(sK2(sK0),X0)
      | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f80])).

fof(f80,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f46,f69])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | v1_subset_1(sK2(sK0),X0)
      | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f65,f88])).

fof(f65,plain,(
    ! [X0] :
      ( sK0 = sK2(sK0)
      | v1_subset_1(sK2(sK0),X0)
      | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:07:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (6733)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (6749)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (6735)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (6731)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (6741)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (6743)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (6739)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.57  % (6731)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (6747)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (6751)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f106,f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ~v1_xboole_0(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27,f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.58    inference(negated_conjecture,[],[f11])).
% 0.22/0.58  fof(f11,conjecture,(
% 0.22/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    v1_xboole_0(sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f105,f100])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    ~v1_subset_1(k1_xboole_0,sK0)),
% 0.22/0.58    inference(superposition,[],[f41,f88])).
% 0.22/0.58  fof(f88,plain,(
% 0.22/0.58    k1_xboole_0 = sK2(sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f86,f71])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    v1_subset_1(sK0,sK0)),
% 0.22/0.58    inference(backward_demodulation,[],[f51,f69])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    sK0 = k1_tarski(sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f68,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.22/0.58    inference(superposition,[],[f42,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    sK0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK1)),
% 0.22/0.58    inference(resolution,[],[f62,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    v1_xboole_0(k1_tarski(sK1)) | sK0 = k1_tarski(sK1)),
% 0.22/0.58    inference(resolution,[],[f60,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    r1_tarski(k1_tarski(sK1),sK0)),
% 0.22/0.58    inference(resolution,[],[f55,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.58    inference(unused_predicate_definition_removal,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(forward_demodulation,[],[f54,f50])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f48,f31])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | v1_xboole_0(sK0)),
% 0.22/0.58    inference(resolution,[],[f43,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    m1_subset_1(sK1,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(subsumption_resolution,[],[f52,f31])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 0.22/0.58    inference(resolution,[],[f44,f32])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f59,f31])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(resolution,[],[f38,f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    v1_zfmisc_1(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    v1_subset_1(k1_tarski(sK1),sK0)),
% 0.22/0.58    inference(backward_demodulation,[],[f33,f50])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ~v1_subset_1(sK0,sK0) | k1_xboole_0 = sK2(sK0)),
% 0.22/0.58    inference(superposition,[],[f41,f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    sK0 = sK2(sK0) | k1_xboole_0 = sK2(sK0)),
% 0.22/0.58    inference(resolution,[],[f61,f39])).
% 0.22/0.58  % (6741)Refutation not found, incomplete strategy% (6741)------------------------------
% 0.22/0.58  % (6741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    v1_xboole_0(sK2(sK0)) | sK0 = sK2(sK0)),
% 0.22/0.58    inference(resolution,[],[f60,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(sK2(X0),X0)) )),
% 0.22/0.58    inference(resolution,[],[f45,f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0] : (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    v1_subset_1(k1_xboole_0,sK0) | v1_xboole_0(sK0)),
% 0.22/0.58    inference(resolution,[],[f95,f99])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(superposition,[],[f40,f88])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | v1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f94,f88])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    ( ! [X0] : (v1_subset_1(k1_xboole_0,X0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f93,f88])).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    ( ! [X0] : (v1_subset_1(sK2(sK0),X0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f90,f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    k1_xboole_0 != sK0),
% 0.22/0.58    inference(superposition,[],[f46,f69])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = sK0 | v1_subset_1(sK2(sK0),X0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(backward_demodulation,[],[f65,f88])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0] : (sK0 = sK2(sK0) | v1_subset_1(sK2(sK0),X0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(resolution,[],[f61,f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (6731)------------------------------
% 0.22/0.58  % (6731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (6731)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (6731)Memory used [KB]: 6268
% 0.22/0.58  % (6731)Time elapsed: 0.139 s
% 0.22/0.58  % (6731)------------------------------
% 0.22/0.58  % (6731)------------------------------
% 0.22/0.58  % (6741)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (6741)Memory used [KB]: 10618
% 0.22/0.58  % (6741)Time elapsed: 0.146 s
% 0.22/0.58  % (6741)------------------------------
% 0.22/0.58  % (6741)------------------------------
% 0.22/0.58  % (6722)Success in time 0.216 s
%------------------------------------------------------------------------------
