%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  57 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   14
%              Number of atoms          :   89 ( 183 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f13,f104,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f18,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f104,plain,(
    ! [X2] : ~ sQ3_eqProxy(k4_xboole_0(X2,sK2),k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f96,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f20])).

fof(f96,plain,(
    ! [X1] : ~ sQ3_eqProxy(k3_subset_1(sK0,sK2),k4_xboole_0(X1,sK2)) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f30,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f20])).

fof(f93,plain,(
    ! [X1] :
      ( ~ sQ3_eqProxy(sK1,sK1)
      | ~ sQ3_eqProxy(k3_subset_1(sK0,sK2),k4_xboole_0(X1,sK2)) ) ),
    inference(resolution,[],[f89,f15])).

fof(f15,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ sQ3_eqProxy(X0,sK1)
      | ~ sQ3_eqProxy(X1,k4_xboole_0(X2,sK2)) ) ),
    inference(resolution,[],[f50,f14])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK1,X2)
      | ~ r1_tarski(X3,X0)
      | ~ sQ3_eqProxy(X3,sK1)
      | ~ sQ3_eqProxy(X0,k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,k4_xboole_0(X1,X0))
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f35,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(sK1,X1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f16,f20])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(k1_xboole_0,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f19,f20])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ r1_tarski(X0,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f20])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (11005)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (11005)Refutation not found, incomplete strategy% (11005)------------------------------
% 0.22/0.48  % (11005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (11005)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (11005)Memory used [KB]: 1535
% 0.22/0.48  % (11005)Time elapsed: 0.050 s
% 0.22/0.48  % (11005)------------------------------
% 0.22/0.48  % (11005)------------------------------
% 0.22/0.48  % (10997)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (10997)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f13,f104,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k4_xboole_0(X0,X1),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f18,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X2] : (~sQ3_eqProxy(k4_xboole_0(X2,sK2),k3_subset_1(sK0,sK2))) )),
% 0.22/0.48    inference(resolution,[],[f96,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.22/0.48    inference(equality_proxy_axiom,[],[f20])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X1] : (~sQ3_eqProxy(k3_subset_1(sK0,sK2),k4_xboole_0(X1,sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f93,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.22/0.48    inference(equality_proxy_axiom,[],[f20])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X1] : (~sQ3_eqProxy(sK1,sK1) | ~sQ3_eqProxy(k3_subset_1(sK0,sK2),k4_xboole_0(X1,sK2))) )),
% 0.22/0.48    inference(resolution,[],[f89,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~sQ3_eqProxy(X0,sK1) | ~sQ3_eqProxy(X1,k4_xboole_0(X2,sK2))) )),
% 0.22/0.48    inference(resolution,[],[f50,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK1,X2) | ~r1_tarski(X3,X0) | ~sQ3_eqProxy(X3,sK1) | ~sQ3_eqProxy(X0,k4_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(resolution,[],[f27,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(sK1,k4_xboole_0(X1,X0)) | ~r1_tarski(sK1,X0)) )),
% 0.22/0.48    inference(resolution,[],[f35,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(sK1,X1) | ~r1_tarski(sK1,X0)) )),
% 0.22/0.48    inference(resolution,[],[f23,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ~sQ3_eqProxy(k1_xboole_0,sK1)),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f16,f20])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    k1_xboole_0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (sQ3_eqProxy(k1_xboole_0,X0) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f19,f20])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | ~sQ3_eqProxy(X2,X3) | ~r1_tarski(X0,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.22/0.48    inference(equality_proxy_axiom,[],[f20])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (10997)------------------------------
% 0.22/0.48  % (10997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10997)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (10997)Memory used [KB]: 6140
% 0.22/0.48  % (10997)Time elapsed: 0.064 s
% 0.22/0.48  % (10997)------------------------------
% 0.22/0.48  % (10997)------------------------------
% 0.22/0.49  % (10991)Success in time 0.119 s
%------------------------------------------------------------------------------
