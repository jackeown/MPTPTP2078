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
% DateTime   : Thu Dec  3 13:20:13 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 171 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 417 expanded)
%              Number of equality atoms :   32 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f858,plain,(
    $false ),
    inference(global_subsumption,[],[f396,f852])).

fof(f852,plain,(
    ~ v1_subset_1(sK0,sK0) ),
    inference(superposition,[],[f44,f737])).

fof(f737,plain,(
    sK0 = sK3(sK0) ),
    inference(unit_resulting_resolution,[],[f71,f725,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f725,plain,(
    r1_tarski(sK0,sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f129,f71,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_zfmisc_1(X0)
      | r1_tarski(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(global_subsumption,[],[f83,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f40,f79])).

fof(f79,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f129,plain,(
    ~ v1_xboole_0(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f44,f43,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f34,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0] : r1_tarski(sK3(X0),X0) ),
    inference(unit_resulting_resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f396,plain,(
    v1_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f33,f395])).

fof(f395,plain,(
    sK0 = k6_domain_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f189,f390])).

fof(f390,plain,(
    sK0 = k3_xboole_0(k6_domain_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f381,f79])).

fof(f381,plain,(
    r1_tarski(sK0,k6_domain_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f34,f214,f375])).

fof(f375,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ v1_zfmisc_1(sK0)
    | r1_tarski(sK0,k6_domain_1(sK0,sK1)) ),
    inference(superposition,[],[f162,f189])).

fof(f162,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k3_xboole_0(X5,X4))
      | ~ v1_zfmisc_1(X4)
      | r1_tarski(X4,X5) ) ),
    inference(global_subsumption,[],[f83,f153])).

fof(f153,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k3_xboole_0(X5,X4))
      | ~ v1_zfmisc_1(X4)
      | v1_xboole_0(X4)
      | r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f40,f46])).

fof(f214,plain,(
    ~ v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(superposition,[],[f95,f203])).

fof(f203,plain,(
    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f35,f32,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f28])).

% (27539)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f32,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f93,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f60,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f60,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f189,plain,(
    k6_domain_1(sK0,sK1) = k3_xboole_0(k6_domain_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f186,f48])).

fof(f186,plain,(
    r1_tarski(k6_domain_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f182,f58])).

fof(f182,plain,(
    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f32,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f33,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (27552)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (27561)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (27542)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (27540)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (27549)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (27541)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (27541)Refutation not found, incomplete strategy% (27541)------------------------------
% 0.20/0.55  % (27541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27541)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27541)Memory used [KB]: 10618
% 0.20/0.55  % (27541)Time elapsed: 0.115 s
% 0.20/0.55  % (27541)------------------------------
% 0.20/0.55  % (27541)------------------------------
% 0.20/0.55  % (27543)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (27564)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (27550)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (27544)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  % (27565)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.57  % (27568)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (27557)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (27555)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (27557)Refutation not found, incomplete strategy% (27557)------------------------------
% 0.20/0.57  % (27557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (27557)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (27557)Memory used [KB]: 10618
% 0.20/0.57  % (27557)Time elapsed: 0.160 s
% 0.20/0.57  % (27557)------------------------------
% 0.20/0.57  % (27557)------------------------------
% 0.20/0.57  % (27560)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (27569)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.57  % (27566)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.57  % (27556)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.58  % (27553)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.58  % (27548)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.58  % (27562)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.58  % (27563)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.58  % (27551)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.58  % (27554)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.73/0.59  % (27545)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.73/0.59  % (27564)Refutation found. Thanks to Tanya!
% 1.73/0.59  % SZS status Theorem for theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f858,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(global_subsumption,[],[f396,f852])).
% 1.73/0.59  fof(f852,plain,(
% 1.73/0.59    ~v1_subset_1(sK0,sK0)),
% 1.73/0.59    inference(superposition,[],[f44,f737])).
% 1.73/0.59  fof(f737,plain,(
% 1.73/0.59    sK0 = sK3(sK0)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f71,f725,f53])).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f5])).
% 1.73/0.59  fof(f5,axiom,(
% 1.73/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.73/0.59  fof(f725,plain,(
% 1.73/0.59    r1_tarski(sK0,sK3(sK0))),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f34,f129,f71,f161])).
% 1.73/0.59  fof(f161,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_zfmisc_1(X0) | r1_tarski(X0,X1) | v1_xboole_0(X1)) )),
% 1.73/0.59    inference(global_subsumption,[],[f83,f151])).
% 1.73/0.59  fof(f151,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | r1_tarski(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.73/0.59    inference(superposition,[],[f40,f79])).
% 1.73/0.59  fof(f79,plain,(
% 1.73/0.59    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.73/0.59    inference(superposition,[],[f48,f46])).
% 1.73/0.59  fof(f46,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f1])).
% 1.73/0.59  fof(f1,axiom,(
% 1.73/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.73/0.59  fof(f48,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f26])).
% 1.73/0.59  fof(f26,plain,(
% 1.73/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f7])).
% 1.73/0.59  fof(f7,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.73/0.59  fof(f40,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f25])).
% 1.73/0.59  fof(f25,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.73/0.59    inference(flattening,[],[f24])).
% 1.73/0.59  fof(f24,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f16])).
% 1.73/0.59  fof(f16,axiom,(
% 1.73/0.59    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 1.73/0.59  fof(f83,plain,(
% 1.73/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.73/0.59    inference(resolution,[],[f55,f42])).
% 1.73/0.59  fof(f42,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f2])).
% 1.73/0.59  fof(f2,axiom,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.73/0.59  fof(f55,plain,(
% 1.73/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f31])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f3])).
% 1.73/0.59  fof(f3,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.73/0.59  fof(f129,plain,(
% 1.73/0.59    ~v1_xboole_0(sK3(sK0))),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f35,f44,f43,f38])).
% 1.73/0.59  fof(f38,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0) | v1_subset_1(X1,X0) | ~v1_xboole_0(X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f22])).
% 1.73/0.59  fof(f22,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.73/0.59    inference(flattening,[],[f21])).
% 1.73/0.59  fof(f21,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f11])).
% 1.73/0.59  fof(f11,axiom,(
% 1.73/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
% 1.73/0.59  fof(f43,plain,(
% 1.73/0.59    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f12])).
% 1.73/0.59  fof(f12,axiom,(
% 1.73/0.59    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 1.73/0.59  fof(f35,plain,(
% 1.73/0.59    ~v1_xboole_0(sK0)),
% 1.73/0.59    inference(cnf_transformation,[],[f20])).
% 1.73/0.59  fof(f20,plain,(
% 1.73/0.59    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.73/0.59    inference(flattening,[],[f19])).
% 1.73/0.59  fof(f19,plain,(
% 1.73/0.59    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f18])).
% 1.73/0.59  fof(f18,negated_conjecture,(
% 1.73/0.59    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.73/0.59    inference(negated_conjecture,[],[f17])).
% 1.73/0.59  fof(f17,conjecture,(
% 1.73/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    v1_zfmisc_1(sK0)),
% 1.73/0.59    inference(cnf_transformation,[],[f20])).
% 1.73/0.59  fof(f71,plain,(
% 1.73/0.59    ( ! [X0] : (r1_tarski(sK3(X0),X0)) )),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f43,f58])).
% 1.73/0.59  fof(f58,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f13])).
% 1.73/0.59  fof(f13,axiom,(
% 1.73/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.73/0.59  fof(f44,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f12])).
% 1.73/0.59  fof(f396,plain,(
% 1.73/0.59    v1_subset_1(sK0,sK0)),
% 1.73/0.59    inference(backward_demodulation,[],[f33,f395])).
% 1.73/0.59  fof(f395,plain,(
% 1.73/0.59    sK0 = k6_domain_1(sK0,sK1)),
% 1.73/0.59    inference(backward_demodulation,[],[f189,f390])).
% 1.73/0.59  fof(f390,plain,(
% 1.73/0.59    sK0 = k3_xboole_0(k6_domain_1(sK0,sK1),sK0)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f381,f79])).
% 1.73/0.59  fof(f381,plain,(
% 1.73/0.59    r1_tarski(sK0,k6_domain_1(sK0,sK1))),
% 1.73/0.59    inference(global_subsumption,[],[f34,f214,f375])).
% 1.73/0.60  fof(f375,plain,(
% 1.73/0.60    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~v1_zfmisc_1(sK0) | r1_tarski(sK0,k6_domain_1(sK0,sK1))),
% 1.73/0.60    inference(superposition,[],[f162,f189])).
% 1.73/0.60  fof(f162,plain,(
% 1.73/0.60    ( ! [X4,X5] : (v1_xboole_0(k3_xboole_0(X5,X4)) | ~v1_zfmisc_1(X4) | r1_tarski(X4,X5)) )),
% 1.73/0.60    inference(global_subsumption,[],[f83,f153])).
% 1.73/0.60  fof(f153,plain,(
% 1.73/0.60    ( ! [X4,X5] : (v1_xboole_0(k3_xboole_0(X5,X4)) | ~v1_zfmisc_1(X4) | v1_xboole_0(X4) | r1_tarski(X4,X5)) )),
% 1.73/0.60    inference(superposition,[],[f40,f46])).
% 1.73/0.60  fof(f214,plain,(
% 1.73/0.60    ~v1_xboole_0(k6_domain_1(sK0,sK1))),
% 1.73/0.60    inference(superposition,[],[f95,f203])).
% 1.73/0.60  fof(f203,plain,(
% 1.73/0.60    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 1.73/0.60    inference(unit_resulting_resolution,[],[f35,f32,f61])).
% 1.73/0.60  fof(f61,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.73/0.60    inference(definition_unfolding,[],[f49,f59])).
% 1.73/0.60  fof(f59,plain,(
% 1.73/0.60    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.73/0.60    inference(definition_unfolding,[],[f37,f47])).
% 1.73/0.60  fof(f47,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f9])).
% 1.73/0.60  fof(f9,axiom,(
% 1.73/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.60  fof(f37,plain,(
% 1.73/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f8])).
% 1.73/0.60  fof(f8,axiom,(
% 1.73/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.73/0.60  fof(f49,plain,(
% 1.73/0.60    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f28])).
% 1.73/0.60  % (27539)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.73/0.60  fof(f28,plain,(
% 1.73/0.60    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.73/0.60    inference(flattening,[],[f27])).
% 1.73/0.60  fof(f27,plain,(
% 1.73/0.60    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f15])).
% 1.73/0.60  fof(f15,axiom,(
% 1.73/0.60    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.73/0.60  fof(f32,plain,(
% 1.73/0.60    m1_subset_1(sK1,sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f20])).
% 1.73/0.60  fof(f95,plain,(
% 1.73/0.60    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 1.73/0.60    inference(unit_resulting_resolution,[],[f93,f39])).
% 1.73/0.60  fof(f39,plain,(
% 1.73/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f23])).
% 1.73/0.60  fof(f23,plain,(
% 1.73/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f4])).
% 1.73/0.60  fof(f4,axiom,(
% 1.73/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.73/0.60  fof(f93,plain,(
% 1.73/0.60    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 1.73/0.60    inference(superposition,[],[f60,f36])).
% 1.73/0.60  fof(f36,plain,(
% 1.73/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.73/0.60    inference(cnf_transformation,[],[f6])).
% 1.73/0.60  fof(f6,axiom,(
% 1.73/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.73/0.60  fof(f60,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 1.73/0.60    inference(definition_unfolding,[],[f45,f59])).
% 1.73/0.60  fof(f45,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f10])).
% 1.73/0.60  fof(f10,axiom,(
% 1.73/0.60    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.73/0.60  fof(f189,plain,(
% 1.73/0.60    k6_domain_1(sK0,sK1) = k3_xboole_0(k6_domain_1(sK0,sK1),sK0)),
% 1.73/0.60    inference(unit_resulting_resolution,[],[f186,f48])).
% 1.73/0.60  fof(f186,plain,(
% 1.73/0.60    r1_tarski(k6_domain_1(sK0,sK1),sK0)),
% 1.73/0.60    inference(unit_resulting_resolution,[],[f182,f58])).
% 1.73/0.60  fof(f182,plain,(
% 1.73/0.60    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.73/0.60    inference(unit_resulting_resolution,[],[f35,f32,f50])).
% 1.73/0.60  fof(f50,plain,(
% 1.73/0.60    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f30])).
% 1.73/0.60  fof(f30,plain,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.73/0.60    inference(flattening,[],[f29])).
% 1.73/0.60  fof(f29,plain,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f14])).
% 1.73/0.60  fof(f14,axiom,(
% 1.73/0.60    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.73/0.60  fof(f33,plain,(
% 1.73/0.60    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f20])).
% 1.73/0.60  % SZS output end Proof for theBenchmark
% 1.73/0.60  % (27564)------------------------------
% 1.73/0.60  % (27564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (27564)Termination reason: Refutation
% 1.73/0.60  
% 1.73/0.60  % (27564)Memory used [KB]: 6652
% 1.73/0.60  % (27564)Time elapsed: 0.158 s
% 1.73/0.60  % (27564)------------------------------
% 1.73/0.60  % (27564)------------------------------
% 1.73/0.60  % (27538)Success in time 0.239 s
%------------------------------------------------------------------------------
