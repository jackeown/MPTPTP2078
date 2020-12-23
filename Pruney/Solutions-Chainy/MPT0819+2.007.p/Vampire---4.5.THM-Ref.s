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
% DateTime   : Thu Dec  3 12:56:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 174 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 475 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31406)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (31399)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (31404)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (31398)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (31393)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (31391)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (31401)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (31395)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f154,plain,(
    $false ),
    inference(resolution,[],[f148,f27])).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f148,plain,(
    ! [X5] : ~ r1_tarski(sK2,X5) ),
    inference(subsumption_resolution,[],[f143,f138])).

fof(f138,plain,(
    ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(subsumption_resolution,[],[f137,f89])).

fof(f89,plain,(
    r1_tarski(k1_relat_1(sK4),sK1) ),
    inference(forward_demodulation,[],[f85,f55])).

fof(f55,plain,(
    sK4 = k7_relat_1(sK4,sK0) ),
    inference(subsumption_resolution,[],[f54,f43])).

fof(f43,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK0) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f44,plain,(
    v4_relat_1(sK4,sK0) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f85,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK4,sK0)),sK1) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X1)),X1) ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(sK4),sK1) ) ),
    inference(subsumption_resolution,[],[f135,f95])).

fof(f95,plain,(
    v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f65,f52])).

fof(f52,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(sK4),X2)
      | v5_relat_1(sK4,X2) ) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f65,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f27,f31])).

fof(f57,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f56,f43])).

fof(f56,plain,
    ( ~ v1_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK4,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(sK4),sK1) ) ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v5_relat_1(sK4,sK3) ) ),
    inference(subsumption_resolution,[],[f77,f43])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ v1_relat_1(sK4)
      | ~ v5_relat_1(sK4,sK3) ) ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK4),sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(resolution,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f28,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f143,plain,(
    ! [X5] :
      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))
      | ~ r1_tarski(sK2,X5) ) ),
    inference(resolution,[],[f73,f57])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(sK4),X2)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK4),X1)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f25,f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:47:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (31390)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (31389)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (31394)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (31388)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (31386)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (31405)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (31384)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (31385)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (31403)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (31387)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (31397)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (31394)Refutation not found, incomplete strategy% (31394)------------------------------
% 0.21/0.52  % (31394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31394)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31394)Memory used [KB]: 10490
% 0.21/0.52  % (31394)Time elapsed: 0.092 s
% 0.21/0.52  % (31394)------------------------------
% 0.21/0.52  % (31394)------------------------------
% 0.21/0.52  % (31405)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (31406)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (31399)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (31404)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (31398)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (31393)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (31391)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31401)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (31395)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f148,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    r1_tarski(sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X5] : (~r1_tarski(sK2,X5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f137,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK4),sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f85,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    sK4 = k7_relat_1(sK4,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f54,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v1_relat_1(sK4)),
% 0.21/0.53    inference(resolution,[],[f25,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK0)),
% 0.21/0.53    inference(resolution,[],[f44,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    v4_relat_1(sK4,sK0)),
% 0.21/0.53    inference(resolution,[],[f25,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(k7_relat_1(sK4,sK0)),sK1)),
% 0.21/0.53    inference(resolution,[],[f51,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f26,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X1)),X1)) )),
% 0.21/0.53    inference(resolution,[],[f43,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(sK4),sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f135,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    v5_relat_1(sK4,sK3)),
% 0.21/0.53    inference(resolution,[],[f65,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(k2_relat_1(sK4),X2) | v5_relat_1(sK4,X2)) )),
% 0.21/0.53    inference(resolution,[],[f43,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(sK4),sK3)),
% 0.21/0.53    inference(resolution,[],[f57,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f27,f31])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(sK4),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f56,f43])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~v1_relat_1(sK4) | r1_tarski(k2_relat_1(sK4),sK2)),
% 0.21/0.53    inference(resolution,[],[f45,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v5_relat_1(sK4,sK2)),
% 0.21/0.53    inference(resolution,[],[f25,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v5_relat_1(sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(sK4),sK1)) )),
% 0.21/0.53    inference(resolution,[],[f79,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v5_relat_1(sK4,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f77,f43])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_relat_1(sK4) | ~v5_relat_1(sK4,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f49,f33])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k2_relat_1(sK4),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.21/0.53    inference(resolution,[],[f28,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ( ! [X5] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) | ~r1_tarski(sK2,X5)) )),
% 0.21/0.53    inference(resolution,[],[f73,f57])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(sK4),X2) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r1_tarski(X2,X1)) )),
% 0.21/0.53    inference(resolution,[],[f47,f31])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k2_relat_1(sK4),X1) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 0.21/0.53    inference(resolution,[],[f25,f29])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (31400)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.53  % (31391)Refutation not found, incomplete strategy% (31391)------------------------------
% 0.21/0.53  % (31391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31391)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31391)Memory used [KB]: 6012
% 0.21/0.53  % (31391)Time elapsed: 0.033 s
% 0.21/0.53  % (31391)------------------------------
% 0.21/0.53  % (31391)------------------------------
% 0.21/0.53  % (31396)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (31405)------------------------------
% 0.21/0.53  % (31405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31402)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (31405)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (31405)Memory used [KB]: 1663
% 0.21/0.53  % (31405)Time elapsed: 0.105 s
% 0.21/0.53  % (31405)------------------------------
% 0.21/0.53  % (31405)------------------------------
% 0.21/0.53  % (31383)Success in time 0.166 s
%------------------------------------------------------------------------------
