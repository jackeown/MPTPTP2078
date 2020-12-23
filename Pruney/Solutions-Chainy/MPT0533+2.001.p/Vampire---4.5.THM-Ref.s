%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:03 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 128 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 532 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(subsumption_resolution,[],[f902,f42])).

fof(f42,plain,(
    ! [X6] : r1_tarski(k8_relat_1(X6,sK2),sK2) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
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
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f902,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f894,f29])).

fof(f29,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f894,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | ~ r1_tarski(k8_relat_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f116,f236])).

fof(f236,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f230,f209])).

fof(f209,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f72,f43])).

fof(f43,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(sK2))
      | v1_relat_1(X7) ) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f72,plain,(
    ! [X4] : m1_subset_1(k8_relat_1(X4,sK2),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f230,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f131,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f131,plain,(
    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X5] : r1_tarski(k2_relat_1(k8_relat_1(X5,sK2)),X5) ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f57,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,(
    ! [X6,X7] :
      ( r1_tarski(k8_relat_1(X7,X6),k8_relat_1(X7,sK3))
      | ~ r1_tarski(X6,sK2) ) ),
    inference(subsumption_resolution,[],[f115,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f43,f36])).

fof(f115,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,sK2)
      | r1_tarski(k8_relat_1(X7,X6),k8_relat_1(X7,sK3))
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f26,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,sK2)
      | r1_tarski(k8_relat_1(X7,X6),k8_relat_1(X7,sK3))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f51,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK3)
      | ~ r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f27,f37])).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24052)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (24055)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (24053)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (24036)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (24032)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (24054)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (24038)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (24044)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (24047)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (24041)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (24045)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (24039)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (24056)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (24035)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (24037)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (24048)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (24033)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (24046)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.30/0.53  % (24053)Refutation not found, incomplete strategy% (24053)------------------------------
% 1.30/0.53  % (24053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (24050)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.30/0.53  % (24042)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.30/0.53  % (24040)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (24049)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.30/0.54  % (24051)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.30/0.54  % (24053)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (24053)Memory used [KB]: 6012
% 1.30/0.54  % (24053)Time elapsed: 0.112 s
% 1.30/0.54  % (24053)------------------------------
% 1.30/0.54  % (24053)------------------------------
% 1.38/0.54  % (24043)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.38/0.58  % (24044)Refutation found. Thanks to Tanya!
% 1.38/0.58  % SZS status Theorem for theBenchmark
% 1.38/0.59  % SZS output start Proof for theBenchmark
% 1.38/0.59  fof(f903,plain,(
% 1.38/0.59    $false),
% 1.38/0.59    inference(subsumption_resolution,[],[f902,f42])).
% 1.38/0.59  fof(f42,plain,(
% 1.38/0.59    ( ! [X6] : (r1_tarski(k8_relat_1(X6,sK2),sK2)) )),
% 1.38/0.59    inference(resolution,[],[f25,f31])).
% 1.38/0.59  fof(f31,plain,(
% 1.38/0.59    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f13])).
% 1.38/0.59  fof(f13,plain,(
% 1.38/0.59    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 1.38/0.59    inference(ennf_transformation,[],[f5])).
% 1.38/0.59  fof(f5,axiom,(
% 1.38/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 1.38/0.59  fof(f25,plain,(
% 1.38/0.59    v1_relat_1(sK2)),
% 1.38/0.59    inference(cnf_transformation,[],[f23])).
% 1.38/0.59  fof(f23,plain,(
% 1.38/0.59    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.38/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21])).
% 1.38/0.59  fof(f21,plain,(
% 1.38/0.59    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.38/0.59    introduced(choice_axiom,[])).
% 1.38/0.59  fof(f22,plain,(
% 1.38/0.59    ? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.38/0.59    introduced(choice_axiom,[])).
% 1.38/0.59  fof(f11,plain,(
% 1.38/0.59    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.38/0.59    inference(flattening,[],[f10])).
% 1.38/0.59  fof(f10,plain,(
% 1.38/0.59    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.38/0.59    inference(ennf_transformation,[],[f9])).
% 1.38/0.59  fof(f9,negated_conjecture,(
% 1.38/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.38/0.59    inference(negated_conjecture,[],[f8])).
% 1.38/0.59  fof(f8,conjecture,(
% 1.38/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).
% 1.38/0.59  fof(f902,plain,(
% 1.38/0.59    ~r1_tarski(k8_relat_1(sK0,sK2),sK2)),
% 1.38/0.59    inference(subsumption_resolution,[],[f894,f29])).
% 1.38/0.59  fof(f29,plain,(
% 1.38/0.59    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 1.38/0.59    inference(cnf_transformation,[],[f23])).
% 1.38/0.59  fof(f894,plain,(
% 1.38/0.59    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | ~r1_tarski(k8_relat_1(sK0,sK2),sK2)),
% 1.38/0.59    inference(superposition,[],[f116,f236])).
% 1.38/0.59  fof(f236,plain,(
% 1.38/0.59    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.38/0.59    inference(subsumption_resolution,[],[f230,f209])).
% 1.38/0.59  fof(f209,plain,(
% 1.38/0.59    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 1.38/0.59    inference(resolution,[],[f72,f43])).
% 1.38/0.59  fof(f43,plain,(
% 1.38/0.59    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(sK2)) | v1_relat_1(X7)) )),
% 1.38/0.59    inference(resolution,[],[f25,f30])).
% 1.38/0.59  fof(f30,plain,(
% 1.38/0.59    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f12])).
% 1.38/0.59  fof(f12,plain,(
% 1.38/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.59    inference(ennf_transformation,[],[f3])).
% 1.38/0.59  fof(f3,axiom,(
% 1.38/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.38/0.59  fof(f72,plain,(
% 1.38/0.59    ( ! [X4] : (m1_subset_1(k8_relat_1(X4,sK2),k1_zfmisc_1(sK2))) )),
% 1.38/0.59    inference(resolution,[],[f42,f36])).
% 1.38/0.59  fof(f36,plain,(
% 1.38/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f24])).
% 1.38/0.59  fof(f24,plain,(
% 1.38/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.38/0.59    inference(nnf_transformation,[],[f2])).
% 1.38/0.59  fof(f2,axiom,(
% 1.38/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.60  fof(f230,plain,(
% 1.38/0.60    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.38/0.60    inference(resolution,[],[f131,f33])).
% 1.38/0.60  fof(f33,plain,(
% 1.38/0.60    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f16])).
% 1.38/0.60  fof(f16,plain,(
% 1.38/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(flattening,[],[f15])).
% 1.38/0.60  fof(f15,plain,(
% 1.38/0.60    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f6])).
% 1.38/0.60  fof(f6,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.38/0.60  fof(f131,plain,(
% 1.38/0.60    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 1.38/0.60    inference(resolution,[],[f57,f41])).
% 1.38/0.60  fof(f41,plain,(
% 1.38/0.60    ( ! [X5] : (r1_tarski(k2_relat_1(k8_relat_1(X5,sK2)),X5)) )),
% 1.38/0.60    inference(resolution,[],[f25,f32])).
% 1.38/0.60  fof(f32,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f14])).
% 1.38/0.60  fof(f14,plain,(
% 1.38/0.60    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f4])).
% 1.38/0.60  fof(f4,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 1.38/0.60  fof(f57,plain,(
% 1.38/0.60    ( ! [X1] : (~r1_tarski(X1,sK0) | r1_tarski(X1,sK1)) )),
% 1.38/0.60    inference(resolution,[],[f28,f37])).
% 1.38/0.60  fof(f37,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f20])).
% 1.38/0.60  fof(f20,plain,(
% 1.38/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.38/0.60    inference(flattening,[],[f19])).
% 1.38/0.60  fof(f19,plain,(
% 1.38/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.38/0.60    inference(ennf_transformation,[],[f1])).
% 1.38/0.60  fof(f1,axiom,(
% 1.38/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.38/0.60  fof(f28,plain,(
% 1.38/0.60    r1_tarski(sK0,sK1)),
% 1.38/0.60    inference(cnf_transformation,[],[f23])).
% 1.38/0.60  fof(f116,plain,(
% 1.38/0.60    ( ! [X6,X7] : (r1_tarski(k8_relat_1(X7,X6),k8_relat_1(X7,sK3)) | ~r1_tarski(X6,sK2)) )),
% 1.38/0.60    inference(subsumption_resolution,[],[f115,f91])).
% 1.38/0.60  fof(f91,plain,(
% 1.38/0.60    ( ! [X0] : (v1_relat_1(X0) | ~r1_tarski(X0,sK2)) )),
% 1.38/0.60    inference(resolution,[],[f43,f36])).
% 1.38/0.60  fof(f115,plain,(
% 1.38/0.60    ( ! [X6,X7] : (~r1_tarski(X6,sK2) | r1_tarski(k8_relat_1(X7,X6),k8_relat_1(X7,sK3)) | ~v1_relat_1(X6)) )),
% 1.38/0.60    inference(subsumption_resolution,[],[f113,f26])).
% 1.38/0.60  fof(f26,plain,(
% 1.38/0.60    v1_relat_1(sK3)),
% 1.38/0.60    inference(cnf_transformation,[],[f23])).
% 1.38/0.60  fof(f113,plain,(
% 1.38/0.60    ( ! [X6,X7] : (~r1_tarski(X6,sK2) | r1_tarski(k8_relat_1(X7,X6),k8_relat_1(X7,sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(X6)) )),
% 1.38/0.60    inference(resolution,[],[f51,f34])).
% 1.38/0.60  fof(f34,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f18])).
% 1.38/0.60  fof(f18,plain,(
% 1.38/0.60    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(flattening,[],[f17])).
% 1.38/0.60  fof(f17,plain,(
% 1.38/0.60    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f7])).
% 1.38/0.60  fof(f7,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 1.38/0.60  fof(f51,plain,(
% 1.38/0.60    ( ! [X1] : (r1_tarski(X1,sK3) | ~r1_tarski(X1,sK2)) )),
% 1.38/0.60    inference(resolution,[],[f27,f37])).
% 1.38/0.60  fof(f27,plain,(
% 1.38/0.60    r1_tarski(sK2,sK3)),
% 1.38/0.60    inference(cnf_transformation,[],[f23])).
% 1.38/0.60  % SZS output end Proof for theBenchmark
% 1.38/0.60  % (24044)------------------------------
% 1.38/0.60  % (24044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.60  % (24044)Termination reason: Refutation
% 1.38/0.60  
% 1.38/0.60  % (24044)Memory used [KB]: 2046
% 1.38/0.60  % (24044)Time elapsed: 0.170 s
% 1.38/0.60  % (24044)------------------------------
% 1.38/0.60  % (24044)------------------------------
% 1.38/0.60  % (24028)Success in time 0.237 s
%------------------------------------------------------------------------------
