%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 125 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  159 ( 284 expanded)
%              Number of equality atoms :   49 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f98,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f48,f54,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f98,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(forward_demodulation,[],[f97,f80])).

fof(f80,plain,(
    k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f75,f64])).

fof(f64,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f61,f63])).

fof(f63,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f62,f40])).

fof(f40,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f62,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f45,f59])).

fof(f59,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f61,plain,(
    ! [X0] : ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f60,f59])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f44,f40])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f75,plain,
    ( v1_subset_1(sK0,sK0)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(superposition,[],[f35,f74])).

fof(f74,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | sK0 = k6_domain_1(sK0,X0)
      | k1_xboole_0 = k6_domain_1(sK0,X0) ) ),
    inference(resolution,[],[f72,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(k6_domain_1(sK0,X0))
      | sK0 = k6_domain_1(sK0,X0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f71,f37])).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(k6_domain_1(sK0,X0))
      | sK0 = k6_domain_1(sK0,X0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f70,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | v1_xboole_0(X0)
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f69,f37])).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f35,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,(
    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f94,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:50:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (24378)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (24380)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (24394)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (24396)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (24390)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (24384)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (24386)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (24400)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (24380)Refutation not found, incomplete strategy% (24380)------------------------------
% 0.20/0.54  % (24380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24380)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24380)Memory used [KB]: 10746
% 0.20/0.54  % (24380)Time elapsed: 0.119 s
% 0.20/0.54  % (24380)------------------------------
% 0.20/0.54  % (24380)------------------------------
% 0.20/0.54  % (24374)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (24378)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f98,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.20/0.54    inference(superposition,[],[f57,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f47,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f49,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    inference(rectify,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f48,f54,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f38,f50])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f97,f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f75,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f61,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.54    inference(forward_demodulation,[],[f62,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(resolution,[],[f45,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(resolution,[],[f43,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f60,f59])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.54    inference(superposition,[],[f44,f40])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    v1_subset_1(sK0,sK0) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.20/0.54    inference(superposition,[],[f35,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    sK0 = k6_domain_1(sK0,sK1) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.20/0.54    inference(resolution,[],[f73,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    m1_subset_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0) | k1_xboole_0 = k6_domain_1(sK0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f72,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | sK0 = k6_domain_1(sK0,X0) | ~m1_subset_1(X0,sK0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f71,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ~v1_xboole_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | sK0 = k6_domain_1(sK0,X0) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0)) )),
% 0.20/0.54    inference(resolution,[],[f70,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f52,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.54    inference(unused_predicate_definition_removal,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f69,f37])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~r1_tarski(X0,sK0) | sK0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f42,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    v1_zfmisc_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f94,f37])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.54    inference(resolution,[],[f58,f34])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f51,f55])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (24378)------------------------------
% 0.20/0.54  % (24378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24378)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (24378)Memory used [KB]: 6268
% 0.20/0.54  % (24378)Time elapsed: 0.121 s
% 0.20/0.54  % (24378)------------------------------
% 0.20/0.54  % (24378)------------------------------
% 0.20/0.54  % (24371)Success in time 0.171 s
%------------------------------------------------------------------------------
