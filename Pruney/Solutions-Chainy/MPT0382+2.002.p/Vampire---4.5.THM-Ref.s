%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  64 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :   75 ( 204 expanded)
%              Number of equality atoms :   24 (  89 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f22,f17,f178,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ3_eqProxy(k3_subset_1(X0,X2),k3_subset_1(X1,X3))
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f178,plain,(
    ~ sQ3_eqProxy(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f75,f10])).

fof(f10,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK1 != sK2
    & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_subset_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ sQ3_eqProxy(k3_subset_1(X0,k3_subset_1(X0,sK1)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ) ),
    inference(resolution,[],[f73,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k3_subset_1(X0,k3_subset_1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f14,f15])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f73,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(X0,sK1)
      | ~ sQ3_eqProxy(X0,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ) ),
    inference(resolution,[],[f45,f11])).

fof(f11,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ sQ3_eqProxy(X0,k3_subset_1(X1,k3_subset_1(X1,sK2)))
      | ~ sQ3_eqProxy(X0,sK1) ) ),
    inference(resolution,[],[f37,f18])).

fof(f37,plain,(
    ! [X2,X1] :
      ( ~ sQ3_eqProxy(X2,sK2)
      | ~ sQ3_eqProxy(X1,sK1)
      | ~ sQ3_eqProxy(X1,X2) ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f15])).

fof(f31,plain,(
    ! [X2] :
      ( ~ sQ3_eqProxy(X2,sK2)
      | ~ sQ3_eqProxy(X2,sK1) ) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(sK1,X0)
      | ~ sQ3_eqProxy(X0,sK2) ) ),
    inference(resolution,[],[f24,f16])).

fof(f16,plain,(
    ~ sQ3_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f13,f15])).

fof(f13,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    sQ3_eqProxy(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f12,f15])).

fof(f12,plain,(
    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (1661)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (1661)Refutation not found, incomplete strategy% (1661)------------------------------
% 0.21/0.45  % (1661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (1644)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (1661)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (1661)Memory used [KB]: 10490
% 0.21/0.46  % (1661)Time elapsed: 0.060 s
% 0.21/0.46  % (1661)------------------------------
% 0.21/0.46  % (1661)------------------------------
% 0.21/0.46  % (1646)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (1638)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (1644)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (1655)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (1647)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f22,f17,f178,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (sQ3_eqProxy(k3_subset_1(X0,X2),k3_subset_1(X1,X3)) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ~sQ3_eqProxy(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k3_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.21/0.47    inference(resolution,[],[f75,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    (sK1 != sK2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (X1 != X2 & k3_subset_1(X0,X1) = k3_subset_1(X0,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X2] : (sK1 != X2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (X1 != X2 & k3_subset_1(X0,X1) = k3_subset_1(X0,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f4])).
% 0.21/0.47  fof(f4,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((X1 != X2 & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X1) = k3_subset_1(X0,X2) => X1 = X2)))),
% 0.21/0.47    inference(negated_conjecture,[],[f2])).
% 0.21/0.47  fof(f2,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X1) = k3_subset_1(X0,X2) => X1 = X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_subset_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~sQ3_eqProxy(k3_subset_1(X0,k3_subset_1(X0,sK1)),k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) )),
% 0.21/0.47    inference(resolution,[],[f73,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sQ3_eqProxy(k3_subset_1(X0,k3_subset_1(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f14,f15])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0] : (~sQ3_eqProxy(X0,sK1) | ~sQ3_eqProxy(X0,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))) )),
% 0.21/0.47    inference(resolution,[],[f45,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~sQ3_eqProxy(X0,k3_subset_1(X1,k3_subset_1(X1,sK2))) | ~sQ3_eqProxy(X0,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f37,f18])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~sQ3_eqProxy(X2,sK2) | ~sQ3_eqProxy(X1,sK1) | ~sQ3_eqProxy(X1,X2)) )),
% 0.21/0.47    inference(resolution,[],[f31,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (sQ3_eqProxy(X0,X2) | ~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f15])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2] : (~sQ3_eqProxy(X2,sK2) | ~sQ3_eqProxy(X2,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f27,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f15])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (~sQ3_eqProxy(sK1,X0) | ~sQ3_eqProxy(X0,sK2)) )),
% 0.21/0.47    inference(resolution,[],[f24,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~sQ3_eqProxy(sK1,sK2)),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f13,f15])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    sK1 != sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    sQ3_eqProxy(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f12,f15])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f15])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (1644)------------------------------
% 0.21/0.47  % (1644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1644)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (1644)Memory used [KB]: 6140
% 0.21/0.47  % (1644)Time elapsed: 0.060 s
% 0.21/0.47  % (1644)------------------------------
% 0.21/0.47  % (1644)------------------------------
% 0.21/0.47  % (1636)Success in time 0.114 s
%------------------------------------------------------------------------------
