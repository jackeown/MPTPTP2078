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
% DateTime   : Thu Dec  3 13:20:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 265 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  167 ( 710 expanded)
%              Number of equality atoms :   44 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f31])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f14])).

% (3886)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f130,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f125])).

fof(f125,plain,(
    ~ v1_subset_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f38,f112])).

fof(f112,plain,(
    k1_xboole_0 = sK2(sK0) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2(sK0) ),
    inference(superposition,[],[f108,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | k1_xboole_0 = sK2(sK0) ),
    inference(resolution,[],[f79,f65])).

fof(f65,plain,
    ( ~ v1_subset_1(sK0,sK0)
    | k1_xboole_0 = sK2(sK0) ),
    inference(superposition,[],[f38,f60])).

fof(f60,plain,
    ( sK0 = sK2(sK0)
    | k1_xboole_0 = sK2(sK0) ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f56,plain,
    ( v1_xboole_0(sK2(sK0))
    | sK0 = sK2(sK0) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(sK2(X0),X0) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | v1_xboole_0(X0)
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f54,f31])).

% (3868)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (3874)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (3876)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f79,plain,
    ( v1_subset_1(sK0,sK0)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(superposition,[],[f29,f76])).

fof(f76,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f73,f49])).

fof(f73,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | sK0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | sK0 = k6_domain_1(sK0,X0)
      | v1_xboole_0(k6_domain_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(k6_domain_1(sK0,X0))
      | sK0 = k6_domain_1(sK0,X0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f42,f43])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f29,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f108,plain,(
    k1_xboole_0 != k6_domain_1(sK0,sK1) ),
    inference(superposition,[],[f51,f106])).

fof(f106,plain,(
    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f104,f31])).

fof(f104,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f46,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f38,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f127,plain,
    ( v1_subset_1(k1_xboole_0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f124,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f124,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f37,f112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:00:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (3871)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (3879)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (3871)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f130,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ~v1_xboole_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  % (3886)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  fof(f14,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.56    inference(negated_conjecture,[],[f13])).
% 0.22/0.56  fof(f13,conjecture,(
% 0.22/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    v1_xboole_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f127,f125])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    ~v1_subset_1(k1_xboole_0,sK0)),
% 0.22/0.56    inference(superposition,[],[f38,f112])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    k1_xboole_0 = sK2(sK0)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f110])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2(sK0)),
% 0.22/0.56    inference(superposition,[],[f108,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    k1_xboole_0 = k6_domain_1(sK0,sK1) | k1_xboole_0 = sK2(sK0)),
% 0.22/0.56    inference(resolution,[],[f79,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ~v1_subset_1(sK0,sK0) | k1_xboole_0 = sK2(sK0)),
% 0.22/0.56    inference(superposition,[],[f38,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    sK0 = sK2(sK0) | k1_xboole_0 = sK2(sK0)),
% 0.22/0.56    inference(resolution,[],[f56,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f44,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    v1_xboole_0(sK2(sK0)) | sK0 = sK2(sK0)),
% 0.22/0.56    inference(resolution,[],[f55,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(sK2(X0),X0)) )),
% 0.22/0.56    inference(resolution,[],[f43,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.56    inference(unused_predicate_definition_removal,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f54,f31])).
% 0.22/0.56  % (3868)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (3874)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (3876)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~r1_tarski(X0,sK0) | sK0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f36,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    v1_zfmisc_1(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    v1_subset_1(sK0,sK0) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.22/0.57    inference(superposition,[],[f29,f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    sK0 = k6_domain_1(sK0,sK1) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.22/0.57    inference(resolution,[],[f73,f49])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    v1_xboole_0(k6_domain_1(sK0,sK1)) | sK0 = k6_domain_1(sK0,sK1)),
% 0.22/0.57    inference(resolution,[],[f58,f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    m1_subset_1(sK1,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0) | v1_xboole_0(k6_domain_1(sK0,X0))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f57,f31])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | sK0 = k6_domain_1(sK0,X0) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.57    inference(resolution,[],[f55,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.57    inference(resolution,[],[f42,f43])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    k1_xboole_0 != k6_domain_1(sK0,sK1)),
% 0.22/0.57    inference(superposition,[],[f51,f106])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.22/0.57    inference(subsumption_resolution,[],[f104,f31])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.22/0.57    inference(resolution,[],[f47,f28])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f41,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f34,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.22/0.57    inference(superposition,[],[f46,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f39,f45])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    v1_subset_1(k1_xboole_0,sK0) | v1_xboole_0(sK0)),
% 0.22/0.57    inference(resolution,[],[f124,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | v1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f35,f32])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.22/0.57  fof(f124,plain,(
% 0.22/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(superposition,[],[f37,f112])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (3871)------------------------------
% 0.22/0.57  % (3871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (3871)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (3871)Memory used [KB]: 6268
% 0.22/0.57  % (3871)Time elapsed: 0.135 s
% 0.22/0.57  % (3871)------------------------------
% 0.22/0.57  % (3871)------------------------------
% 0.22/0.57  % (3864)Success in time 0.203 s
%------------------------------------------------------------------------------
