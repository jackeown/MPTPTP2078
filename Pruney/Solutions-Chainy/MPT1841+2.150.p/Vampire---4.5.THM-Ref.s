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
% DateTime   : Thu Dec  3 13:20:29 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 149 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 470 expanded)
%              Number of equality atoms :   34 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(subsumption_resolution,[],[f89,f65])).

fof(f65,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f62,f64])).

fof(f64,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f63,f45])).

fof(f45,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f63,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f62,plain,(
    ! [X0] : ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f61,f59])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f49,f45])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f89,plain,(
    v1_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f75,f87])).

fof(f87,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f85,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f52,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f85,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f84,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f84,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f83,f79])).

fof(f79,plain,(
    r1_tarski(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f77,f74])).

fof(f74,plain,(
    k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f73,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

% (2249)Refutation not found, incomplete strategy% (2249)------------------------------
% (2249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

% (2249)Termination reason: Refutation not found, incomplete strategy

% (2249)Memory used [KB]: 10618
% (2249)Time elapsed: 0.081 s
% (2249)------------------------------
% (2249)------------------------------
fof(f73,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f77,plain,(
    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f38])).

fof(f76,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f75,plain,(
    v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f40,f74])).

fof(f40,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:40:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (2231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (2242)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (2234)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (2255)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (2232)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (2242)Refutation not found, incomplete strategy% (2242)------------------------------
% 0.22/0.52  % (2242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2239)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (2231)Refutation not found, incomplete strategy% (2231)------------------------------
% 1.26/0.53  % (2231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (2231)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  % (2250)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.53  
% 1.26/0.53  % (2231)Memory used [KB]: 6268
% 1.26/0.53  % (2231)Time elapsed: 0.102 s
% 1.26/0.53  % (2231)------------------------------
% 1.26/0.53  % (2231)------------------------------
% 1.26/0.53  % (2242)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (2242)Memory used [KB]: 6268
% 1.26/0.53  % (2242)Time elapsed: 0.095 s
% 1.26/0.53  % (2242)------------------------------
% 1.26/0.53  % (2242)------------------------------
% 1.26/0.53  % (2249)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (2234)Refutation found. Thanks to Tanya!
% 1.26/0.53  % SZS status Theorem for theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f94,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(subsumption_resolution,[],[f89,f65])).
% 1.26/0.53  fof(f65,plain,(
% 1.26/0.53    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.26/0.53    inference(backward_demodulation,[],[f62,f64])).
% 1.26/0.53  fof(f64,plain,(
% 1.26/0.53    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.26/0.53    inference(forward_demodulation,[],[f63,f45])).
% 1.26/0.53  fof(f45,plain,(
% 1.26/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f15])).
% 1.26/0.53  fof(f15,axiom,(
% 1.26/0.53    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.26/0.53  fof(f63,plain,(
% 1.26/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 1.26/0.53    inference(resolution,[],[f50,f59])).
% 1.26/0.53  fof(f59,plain,(
% 1.26/0.53    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 1.26/0.53    inference(resolution,[],[f48,f44])).
% 1.26/0.53  fof(f44,plain,(
% 1.26/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.26/0.53    inference(cnf_transformation,[],[f21])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.26/0.53    inference(pure_predicate_removal,[],[f14])).
% 1.26/0.53  fof(f14,axiom,(
% 1.26/0.53    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.26/0.53  fof(f48,plain,(
% 1.26/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f26])).
% 1.26/0.53  fof(f26,plain,(
% 1.26/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f12])).
% 1.26/0.53  fof(f12,axiom,(
% 1.26/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f28,plain,(
% 1.26/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,axiom,(
% 1.26/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.26/0.53  fof(f62,plain,(
% 1.26/0.53    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)) )),
% 1.26/0.53    inference(subsumption_resolution,[],[f61,f59])).
% 1.26/0.53  fof(f61,plain,(
% 1.26/0.53    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 1.26/0.53    inference(superposition,[],[f49,f45])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f27])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f10])).
% 1.26/0.53  fof(f10,axiom,(
% 1.26/0.53    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 1.26/0.53  fof(f89,plain,(
% 1.26/0.53    v1_subset_1(sK0,sK0)),
% 1.26/0.53    inference(backward_demodulation,[],[f75,f87])).
% 1.26/0.53  fof(f87,plain,(
% 1.26/0.53    sK0 = k1_tarski(sK1)),
% 1.26/0.53    inference(subsumption_resolution,[],[f85,f60])).
% 1.26/0.53  fof(f60,plain,(
% 1.26/0.53    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 1.26/0.53    inference(superposition,[],[f52,f51])).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f19])).
% 1.26/0.53  fof(f19,plain,(
% 1.26/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.26/0.53    inference(rectify,[],[f2])).
% 1.26/0.53  fof(f2,axiom,(
% 1.26/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.26/0.53  fof(f52,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f7])).
% 1.26/0.53  fof(f7,axiom,(
% 1.26/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.26/0.53  fof(f85,plain,(
% 1.26/0.53    sK0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK1)),
% 1.26/0.53    inference(resolution,[],[f84,f69])).
% 1.26/0.53  fof(f69,plain,(
% 1.26/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.26/0.53    inference(resolution,[],[f58,f42])).
% 1.26/0.53  fof(f42,plain,(
% 1.26/0.53    v1_xboole_0(k1_xboole_0)),
% 1.26/0.53    inference(cnf_transformation,[],[f1])).
% 1.26/0.53  fof(f1,axiom,(
% 1.26/0.53    v1_xboole_0(k1_xboole_0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.26/0.53  fof(f58,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f34,plain,(
% 1.26/0.53    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f3])).
% 1.26/0.53  fof(f3,axiom,(
% 1.26/0.53    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.26/0.53  fof(f84,plain,(
% 1.26/0.53    v1_xboole_0(k1_tarski(sK1)) | sK0 = k1_tarski(sK1)),
% 1.26/0.53    inference(resolution,[],[f83,f79])).
% 1.26/0.53  fof(f79,plain,(
% 1.26/0.53    r1_tarski(k1_tarski(sK1),sK0)),
% 1.26/0.53    inference(resolution,[],[f78,f57])).
% 1.26/0.53  fof(f57,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f33])).
% 1.26/0.53  fof(f33,plain,(
% 1.26/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.26/0.53    inference(ennf_transformation,[],[f20])).
% 1.26/0.53  fof(f20,plain,(
% 1.26/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.26/0.53    inference(unused_predicate_definition_removal,[],[f8])).
% 1.26/0.54  fof(f8,axiom,(
% 1.26/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.26/0.54  fof(f78,plain,(
% 1.26/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(forward_demodulation,[],[f77,f74])).
% 1.26/0.54  fof(f74,plain,(
% 1.26/0.54    k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 1.26/0.54    inference(subsumption_resolution,[],[f73,f38])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ~v1_xboole_0(sK0)),
% 1.26/0.54    inference(cnf_transformation,[],[f37])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f36,f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f36,plain,(
% 1.26/0.54    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f23,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.26/0.54    inference(flattening,[],[f22])).
% 1.26/0.54  fof(f22,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.26/0.54    inference(ennf_transformation,[],[f18])).
% 1.26/0.54  fof(f18,negated_conjecture,(
% 1.26/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.26/0.54    inference(negated_conjecture,[],[f17])).
% 1.26/0.54  % (2249)Refutation not found, incomplete strategy% (2249)------------------------------
% 1.26/0.54  % (2249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  fof(f17,conjecture,(
% 1.26/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.26/0.54  % (2249)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (2249)Memory used [KB]: 10618
% 1.26/0.54  % (2249)Time elapsed: 0.081 s
% 1.26/0.54  % (2249)------------------------------
% 1.26/0.54  % (2249)------------------------------
% 1.26/0.54  fof(f73,plain,(
% 1.26/0.54    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | v1_xboole_0(sK0)),
% 1.26/0.54    inference(resolution,[],[f55,f39])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    m1_subset_1(sK1,sK0)),
% 1.26/0.54    inference(cnf_transformation,[],[f37])).
% 1.26/0.54  fof(f55,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f30])).
% 1.26/0.54  fof(f30,plain,(
% 1.26/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.26/0.54    inference(flattening,[],[f29])).
% 1.26/0.54  fof(f29,plain,(
% 1.26/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f13])).
% 1.26/0.54  fof(f13,axiom,(
% 1.26/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.26/0.54  fof(f77,plain,(
% 1.26/0.54    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(subsumption_resolution,[],[f76,f38])).
% 1.26/0.54  fof(f76,plain,(
% 1.26/0.54    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 1.26/0.54    inference(resolution,[],[f56,f39])).
% 1.26/0.54  fof(f56,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f32])).
% 1.26/0.54  fof(f32,plain,(
% 1.26/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.26/0.54    inference(flattening,[],[f31])).
% 1.26/0.54  fof(f31,plain,(
% 1.26/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f11])).
% 1.26/0.54  fof(f11,axiom,(
% 1.26/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.26/0.54  fof(f83,plain,(
% 1.26/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(subsumption_resolution,[],[f82,f38])).
% 1.26/0.54  fof(f82,plain,(
% 1.26/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(resolution,[],[f47,f41])).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    v1_zfmisc_1(sK0)),
% 1.26/0.54    inference(cnf_transformation,[],[f37])).
% 1.26/0.54  fof(f47,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  fof(f25,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.26/0.54    inference(flattening,[],[f24])).
% 1.26/0.54  fof(f24,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.26/0.54    inference(ennf_transformation,[],[f16])).
% 1.26/0.54  fof(f16,axiom,(
% 1.26/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.26/0.54  fof(f75,plain,(
% 1.26/0.54    v1_subset_1(k1_tarski(sK1),sK0)),
% 1.26/0.54    inference(backward_demodulation,[],[f40,f74])).
% 1.26/0.54  fof(f40,plain,(
% 1.26/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.26/0.54    inference(cnf_transformation,[],[f37])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (2234)------------------------------
% 1.26/0.54  % (2234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (2234)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (2234)Memory used [KB]: 6268
% 1.26/0.54  % (2234)Time elapsed: 0.114 s
% 1.26/0.54  % (2234)------------------------------
% 1.26/0.54  % (2234)------------------------------
% 1.26/0.54  % (2226)Success in time 0.166 s
%------------------------------------------------------------------------------
