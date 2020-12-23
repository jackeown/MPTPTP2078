%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  94 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 300 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(subsumption_resolution,[],[f200,f21])).

fof(f21,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f200,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f198,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(sK2,X0),X1)
      | ~ r1_tarski(sK2,X1) ) ),
    inference(superposition,[],[f32,f45])).

fof(f45,plain,(
    ! [X1] : sK2 = k2_xboole_0(k7_relat_1(sK2,X1),sK2) ),
    inference(resolution,[],[f41,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_xboole_0(k7_relat_1(X0,X1),X0) = X0 ) ),
    inference(resolution,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f198,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),sK3) ),
    inference(subsumption_resolution,[],[f191,f20])).

fof(f20,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f191,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK3) ),
    inference(resolution,[],[f126,f23])).

fof(f23,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f126,plain,(
    ! [X2] :
      ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k7_relat_1(sK2,sK0),X2) ) ),
    inference(subsumption_resolution,[],[f122,f55])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(subsumption_resolution,[],[f54,f20])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f53,f21])).

fof(f53,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK2,X2)
      | v1_relat_1(k7_relat_1(sK2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f122,plain,(
    ! [X2] :
      ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k7_relat_1(sK2,sK0),X2)
      | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f27,f108])).

fof(f108,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f75,f24])).

fof(f75,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,sK0) = k7_relat_1(k7_relat_1(X1,sK0),sK1) ) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:24 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.47  % (13601)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (13610)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.49  % (13599)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (13597)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (13599)Refutation not found, incomplete strategy% (13599)------------------------------
% 0.20/0.49  % (13599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13599)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13599)Memory used [KB]: 10490
% 0.20/0.49  % (13599)Time elapsed: 0.071 s
% 0.20/0.49  % (13599)------------------------------
% 0.20/0.49  % (13599)------------------------------
% 0.20/0.49  % (13609)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.49  % (13611)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (13598)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (13600)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (13612)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.50  % (13607)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (13602)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (13596)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (13617)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (13614)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (13605)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (13603)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (13616)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (13603)Refutation not found, incomplete strategy% (13603)------------------------------
% 0.20/0.51  % (13603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13603)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13603)Memory used [KB]: 6140
% 0.20/0.51  % (13603)Time elapsed: 0.065 s
% 0.20/0.51  % (13603)------------------------------
% 0.20/0.51  % (13603)------------------------------
% 0.20/0.51  % (13604)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (13616)Refutation not found, incomplete strategy% (13616)------------------------------
% 0.20/0.51  % (13616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13616)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13616)Memory used [KB]: 6140
% 0.20/0.51  % (13616)Time elapsed: 0.097 s
% 0.20/0.51  % (13616)------------------------------
% 0.20/0.51  % (13616)------------------------------
% 0.20/0.51  % (13604)Refutation not found, incomplete strategy% (13604)------------------------------
% 0.20/0.51  % (13604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13604)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13604)Memory used [KB]: 10490
% 0.20/0.51  % (13604)Time elapsed: 0.096 s
% 0.20/0.51  % (13604)------------------------------
% 0.20/0.51  % (13604)------------------------------
% 0.20/0.51  % (13612)Refutation not found, incomplete strategy% (13612)------------------------------
% 0.20/0.51  % (13612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13612)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13612)Memory used [KB]: 1535
% 0.20/0.51  % (13612)Time elapsed: 0.105 s
% 0.20/0.51  % (13612)------------------------------
% 0.20/0.51  % (13612)------------------------------
% 0.20/0.51  % (13615)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (13619)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (13608)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (13619)Refutation not found, incomplete strategy% (13619)------------------------------
% 0.20/0.51  % (13619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13619)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13619)Memory used [KB]: 10618
% 0.20/0.51  % (13619)Time elapsed: 0.067 s
% 0.20/0.51  % (13619)------------------------------
% 0.20/0.51  % (13619)------------------------------
% 0.20/0.51  % (13609)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f200,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    r1_tarski(sK2,sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    ~r1_tarski(sK2,sK3)),
% 0.20/0.51    inference(resolution,[],[f198,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k7_relat_1(sK2,X0),X1) | ~r1_tarski(sK2,X1)) )),
% 0.20/0.51    inference(superposition,[],[f32,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X1] : (sK2 = k2_xboole_0(k7_relat_1(sK2,X1),sK2)) )),
% 0.20/0.51    inference(resolution,[],[f41,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_xboole_0(k7_relat_1(X0,X1),X0) = X0) )),
% 0.20/0.51    inference(resolution,[],[f28,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ~r1_tarski(k7_relat_1(sK2,sK0),sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f191,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    v1_relat_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~v1_relat_1(sK3) | ~r1_tarski(k7_relat_1(sK2,sK0),sK3)),
% 0.20/0.51    inference(resolution,[],[f126,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) | ~v1_relat_1(X2) | ~r1_tarski(k7_relat_1(sK2,sK0),X2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f122,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f54,f20])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(sK3)) )),
% 0.20/0.51    inference(resolution,[],[f53,f21])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r1_tarski(sK2,X2) | v1_relat_1(k7_relat_1(sK2,X3)) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(resolution,[],[f48,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f25,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) | ~v1_relat_1(X2) | ~r1_tarski(k7_relat_1(sK2,sK0),X2) | ~v1_relat_1(k7_relat_1(sK2,sK0))) )),
% 0.20/0.51    inference(superposition,[],[f27,f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f75,f24])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X1] : (~v1_relat_1(X1) | k7_relat_1(X1,sK0) = k7_relat_1(k7_relat_1(X1,sK0),sK1)) )),
% 0.20/0.51    inference(resolution,[],[f31,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (13609)------------------------------
% 0.20/0.51  % (13609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13609)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (13609)Memory used [KB]: 6396
% 0.20/0.51  % (13609)Time elapsed: 0.097 s
% 0.20/0.51  % (13609)------------------------------
% 0.20/0.51  % (13609)------------------------------
% 0.20/0.51  % (13606)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (13595)Success in time 0.16 s
%------------------------------------------------------------------------------
