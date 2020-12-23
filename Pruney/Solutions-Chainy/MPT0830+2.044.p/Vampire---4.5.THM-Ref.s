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
% DateTime   : Thu Dec  3 12:56:51 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 168 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  134 ( 358 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f571,plain,(
    $false ),
    inference(resolution,[],[f534,f147])).

fof(f147,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f24,f144])).

fof(f144,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK0,sK2,sK3,X0) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f24,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f534,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(subsumption_resolution,[],[f533,f44])).

fof(f44,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f41,f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f533,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f531,f51])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f47,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f25])).

fof(f531,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X0))
      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f530,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f530,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK2) ),
    inference(resolution,[],[f529,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f529,plain,(
    ! [X2] : m1_subset_1(k2_relat_1(k7_relat_1(sK3,X2)),k1_zfmisc_1(sK2)) ),
    inference(backward_demodulation,[],[f525,f526])).

fof(f526,plain,(
    ! [X3] : k2_relset_1(sK0,sK2,k7_relat_1(sK3,X3)) = k2_relat_1(k7_relat_1(sK3,X3)) ),
    inference(resolution,[],[f523,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f523,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f518,f44])).

fof(f518,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f516,f27])).

fof(f516,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,k2_zfmisc_1(sK0,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,k2_zfmisc_1(sK0,sK2)) ) ),
    inference(resolution,[],[f483,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f483,plain,(
    ! [X33,X32] :
      ( r2_hidden(sK4(X32,X33),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(X32,X33)
      | ~ r1_tarski(X32,sK3) ) ),
    inference(resolution,[],[f123,f38])).

fof(f38,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f33,f23])).

fof(f123,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK4(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f53,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f525,plain,(
    ! [X2] : m1_subset_1(k2_relset_1(sK0,sK2,k7_relat_1(sK3,X2)),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f523,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f36,f32])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:49:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (10855)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (10851)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (10865)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (10853)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (10852)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (10870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (10862)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (10869)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (10856)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (10858)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (10856)Refutation not found, incomplete strategy% (10856)------------------------------
% 0.22/0.54  % (10856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10856)Memory used [KB]: 10746
% 0.22/0.54  % (10856)Time elapsed: 0.125 s
% 0.22/0.54  % (10856)------------------------------
% 0.22/0.54  % (10856)------------------------------
% 0.22/0.54  % (10877)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (10876)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (10860)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (10858)Refutation not found, incomplete strategy% (10858)------------------------------
% 0.22/0.54  % (10858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  % (10849)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  
% 0.22/0.54  % (10854)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (10858)Memory used [KB]: 10618
% 0.22/0.54  % (10858)Time elapsed: 0.134 s
% 0.22/0.54  % (10858)------------------------------
% 0.22/0.54  % (10858)------------------------------
% 0.22/0.54  % (10870)Refutation not found, incomplete strategy% (10870)------------------------------
% 0.22/0.54  % (10870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10870)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10870)Memory used [KB]: 10746
% 0.22/0.54  % (10870)Time elapsed: 0.088 s
% 0.22/0.54  % (10870)------------------------------
% 0.22/0.54  % (10870)------------------------------
% 0.22/0.54  % (10848)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (10850)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (10867)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (10850)Refutation not found, incomplete strategy% (10850)------------------------------
% 0.22/0.54  % (10850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10850)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10850)Memory used [KB]: 10746
% 0.22/0.54  % (10850)Time elapsed: 0.126 s
% 0.22/0.54  % (10850)------------------------------
% 0.22/0.54  % (10850)------------------------------
% 0.22/0.54  % (10861)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (10872)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (10868)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (10864)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (10871)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (10875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (10857)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (10873)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (10863)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.65/0.59  % (10859)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.65/0.59  % (10859)Refutation not found, incomplete strategy% (10859)------------------------------
% 1.65/0.59  % (10859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (10866)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.65/0.59  % (10859)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (10859)Memory used [KB]: 10618
% 1.65/0.59  % (10859)Time elapsed: 0.148 s
% 1.65/0.59  % (10859)------------------------------
% 1.65/0.59  % (10859)------------------------------
% 1.65/0.59  % (10874)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.59  % (10854)Refutation found. Thanks to Tanya!
% 1.65/0.59  % SZS status Theorem for theBenchmark
% 1.65/0.59  % SZS output start Proof for theBenchmark
% 1.65/0.59  fof(f571,plain,(
% 1.65/0.59    $false),
% 1.65/0.59    inference(resolution,[],[f534,f147])).
% 1.65/0.59  fof(f147,plain,(
% 1.65/0.59    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.65/0.59    inference(backward_demodulation,[],[f24,f144])).
% 1.65/0.59  fof(f144,plain,(
% 1.65/0.59    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK0,sK2,sK3,X0)) )),
% 1.65/0.59    inference(resolution,[],[f37,f23])).
% 1.65/0.59  fof(f23,plain,(
% 1.65/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.65/0.59    inference(cnf_transformation,[],[f13])).
% 1.65/0.59  fof(f13,plain,(
% 1.65/0.59    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.65/0.59    inference(ennf_transformation,[],[f12])).
% 1.65/0.59  fof(f12,negated_conjecture,(
% 1.65/0.59    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.65/0.59    inference(negated_conjecture,[],[f11])).
% 1.65/0.59  fof(f11,conjecture,(
% 1.65/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 1.65/0.59  fof(f37,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f22])).
% 1.65/0.59  fof(f22,plain,(
% 1.65/0.59    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f9])).
% 1.65/0.59  fof(f9,axiom,(
% 1.65/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 1.65/0.59  fof(f24,plain,(
% 1.65/0.59    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.65/0.59    inference(cnf_transformation,[],[f13])).
% 1.65/0.59  fof(f534,plain,(
% 1.65/0.59    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.65/0.59    inference(subsumption_resolution,[],[f533,f44])).
% 1.65/0.59  fof(f44,plain,(
% 1.65/0.59    v1_relat_1(sK3)),
% 1.65/0.59    inference(resolution,[],[f41,f23])).
% 1.65/0.59  fof(f41,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.65/0.59    inference(resolution,[],[f25,f26])).
% 1.65/0.59  fof(f26,plain,(
% 1.65/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f4])).
% 1.65/0.59  fof(f4,axiom,(
% 1.65/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.65/0.59  fof(f25,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f14])).
% 1.65/0.59  fof(f14,plain,(
% 1.65/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f3])).
% 1.65/0.59  fof(f3,axiom,(
% 1.65/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.65/0.59  fof(f533,plain,(
% 1.65/0.59    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_relat_1(sK3)) )),
% 1.65/0.59    inference(subsumption_resolution,[],[f531,f51])).
% 1.65/0.59  fof(f51,plain,(
% 1.65/0.59    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.65/0.59    inference(subsumption_resolution,[],[f49,f44])).
% 1.65/0.59  fof(f49,plain,(
% 1.65/0.59    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 1.65/0.59    inference(resolution,[],[f47,f27])).
% 1.65/0.59  fof(f27,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f15])).
% 1.65/0.59  fof(f15,plain,(
% 1.65/0.59    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.65/0.59    inference(ennf_transformation,[],[f6])).
% 1.65/0.59  fof(f6,axiom,(
% 1.65/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.65/0.59  fof(f47,plain,(
% 1.65/0.59    ( ! [X0] : (~r1_tarski(X0,sK3) | v1_relat_1(X0)) )),
% 1.65/0.59    inference(resolution,[],[f46,f32])).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f2])).
% 1.65/0.59  fof(f2,axiom,(
% 1.65/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.59  fof(f46,plain,(
% 1.65/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK3)) | v1_relat_1(X0)) )),
% 1.65/0.59    inference(resolution,[],[f44,f25])).
% 1.65/0.59  fof(f531,plain,(
% 1.65/0.59    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_relat_1(sK3)) )),
% 1.65/0.59    inference(resolution,[],[f530,f209])).
% 1.65/0.59  fof(f209,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2) | ~v1_relat_1(k7_relat_1(X0,X1)) | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 1.65/0.59    inference(resolution,[],[f34,f28])).
% 1.65/0.59  fof(f28,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f16])).
% 1.65/0.59  fof(f16,plain,(
% 1.65/0.59    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.65/0.59    inference(ennf_transformation,[],[f5])).
% 1.65/0.59  fof(f5,axiom,(
% 1.65/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.65/0.59  fof(f34,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f19])).
% 1.65/0.59  fof(f19,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.65/0.59    inference(flattening,[],[f18])).
% 1.65/0.59  fof(f18,plain,(
% 1.65/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.65/0.59    inference(ennf_transformation,[],[f10])).
% 1.65/0.59  fof(f10,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.65/0.59  fof(f530,plain,(
% 1.65/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK2)) )),
% 1.65/0.59    inference(resolution,[],[f529,f33])).
% 1.65/0.59  fof(f33,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f2])).
% 1.65/0.59  fof(f529,plain,(
% 1.65/0.59    ( ! [X2] : (m1_subset_1(k2_relat_1(k7_relat_1(sK3,X2)),k1_zfmisc_1(sK2))) )),
% 1.65/0.59    inference(backward_demodulation,[],[f525,f526])).
% 1.65/0.59  fof(f526,plain,(
% 1.65/0.59    ( ! [X3] : (k2_relset_1(sK0,sK2,k7_relat_1(sK3,X3)) = k2_relat_1(k7_relat_1(sK3,X3))) )),
% 1.65/0.59    inference(resolution,[],[f523,f84])).
% 1.65/0.59  fof(f84,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.65/0.59    inference(resolution,[],[f35,f32])).
% 1.65/0.59  fof(f35,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f20])).
% 1.65/0.59  fof(f20,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f8])).
% 1.65/0.59  fof(f8,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.65/0.59  fof(f523,plain,(
% 1.65/0.59    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2))) )),
% 1.65/0.59    inference(subsumption_resolution,[],[f518,f44])).
% 1.65/0.59  fof(f518,plain,(
% 1.65/0.59    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2)) | ~v1_relat_1(sK3)) )),
% 1.65/0.59    inference(resolution,[],[f516,f27])).
% 1.65/0.59  fof(f516,plain,(
% 1.65/0.59    ( ! [X0] : (~r1_tarski(X0,sK3) | r1_tarski(X0,k2_zfmisc_1(sK0,sK2))) )),
% 1.65/0.59    inference(duplicate_literal_removal,[],[f514])).
% 1.65/0.59  fof(f514,plain,(
% 1.65/0.59    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(X0,sK3) | r1_tarski(X0,k2_zfmisc_1(sK0,sK2))) )),
% 1.65/0.59    inference(resolution,[],[f483,f31])).
% 1.65/0.59  fof(f31,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  fof(f17,plain,(
% 1.65/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f1])).
% 1.65/0.59  fof(f1,axiom,(
% 1.65/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.65/0.59  fof(f483,plain,(
% 1.65/0.59    ( ! [X33,X32] : (r2_hidden(sK4(X32,X33),k2_zfmisc_1(sK0,sK2)) | r1_tarski(X32,X33) | ~r1_tarski(X32,sK3)) )),
% 1.65/0.59    inference(resolution,[],[f123,f38])).
% 1.65/0.59  fof(f38,plain,(
% 1.65/0.59    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.65/0.59    inference(resolution,[],[f33,f23])).
% 1.65/0.59  fof(f123,plain,(
% 1.65/0.59    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK4(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 1.65/0.59    inference(resolution,[],[f53,f29])).
% 1.65/0.59  fof(f29,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  fof(f53,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(resolution,[],[f29,f30])).
% 1.65/0.59  fof(f30,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  fof(f525,plain,(
% 1.65/0.59    ( ! [X2] : (m1_subset_1(k2_relset_1(sK0,sK2,k7_relat_1(sK3,X2)),k1_zfmisc_1(sK2))) )),
% 1.65/0.59    inference(resolution,[],[f523,f113])).
% 1.65/0.59  fof(f113,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.65/0.59    inference(resolution,[],[f36,f32])).
% 1.65/0.59  fof(f36,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f21])).
% 1.65/0.59  fof(f21,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f7])).
% 1.65/0.59  fof(f7,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (10854)------------------------------
% 1.65/0.59  % (10854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (10854)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (10854)Memory used [KB]: 7036
% 1.65/0.59  % (10854)Time elapsed: 0.149 s
% 1.65/0.59  % (10854)------------------------------
% 1.65/0.59  % (10854)------------------------------
% 1.82/0.61  % (10846)Success in time 0.24 s
%------------------------------------------------------------------------------
