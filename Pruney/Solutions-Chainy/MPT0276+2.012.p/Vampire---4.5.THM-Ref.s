%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  69 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 213 expanded)
%              Number of equality atoms :   57 ( 144 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f29,f57,f15,f26,f65,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(k1_tarski(X2),X0)
      | sQ3_eqProxy(k2_tarski(X1,X2),X0)
      | sQ3_eqProxy(k1_tarski(X1),X0)
      | sQ3_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f16,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f65,plain,(
    ~ sQ3_eqProxy(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f56,plain,(
    ! [X8] :
      ( ~ sQ3_eqProxy(sK0,X8)
      | ~ sQ3_eqProxy(k1_tarski(X8),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    ~ sQ3_eqProxy(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k1_tarski(sK0)) ),
    inference(equality_proxy_replacement,[],[f12,f25])).

fof(f12,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f48,plain,(
    ! [X6,X4,X5] :
      ( sQ3_eqProxy(X5,k1_tarski(X6))
      | ~ sQ3_eqProxy(X6,X4)
      | ~ sQ3_eqProxy(k1_tarski(X4),X5) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f45,plain,(
    ! [X6,X7,X5] :
      ( sQ3_eqProxy(k1_tarski(X7),X6)
      | ~ sQ3_eqProxy(k1_tarski(X5),X6)
      | ~ sQ3_eqProxy(X7,X5) ) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_tarski(X0),k1_tarski(X1))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | ~ sQ3_eqProxy(X1,X2)
      | sQ3_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f26,plain,(
    ~ sQ3_eqProxy(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(equality_proxy_replacement,[],[f14,f25])).

fof(f14,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f57,plain,(
    ~ sQ3_eqProxy(k1_tarski(sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X7] :
      ( ~ sQ3_eqProxy(sK1,X7)
      | ~ sQ3_eqProxy(k1_tarski(X7),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    ~ sQ3_eqProxy(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k1_tarski(sK1)) ),
    inference(equality_proxy_replacement,[],[f13,f25])).

fof(f13,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(equality_proxy_replacement,[],[f11,f25])).

fof(f11,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:21:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (19578)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (19578)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f29,f57,f15,f26,f65,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (sQ3_eqProxy(k1_tarski(X2),X0) | sQ3_eqProxy(k2_tarski(X1,X2),X0) | sQ3_eqProxy(k1_tarski(X1),X0) | sQ3_eqProxy(k1_xboole_0,X0) | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f16,f25,f25,f25,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.46    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.46    inference(nnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ~sQ3_eqProxy(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.46    inference(resolution,[],[f56,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.21/0.46    inference(equality_proxy_axiom,[],[f25])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X8] : (~sQ3_eqProxy(sK0,X8) | ~sQ3_eqProxy(k1_tarski(X8),k4_xboole_0(k2_tarski(sK0,sK1),sK2))) )),
% 0.21/0.46    inference(resolution,[],[f48,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ~sQ3_eqProxy(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k1_tarski(sK0))),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f12,f25])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X6,X4,X5] : (sQ3_eqProxy(X5,k1_tarski(X6)) | ~sQ3_eqProxy(X6,X4) | ~sQ3_eqProxy(k1_tarski(X4),X5)) )),
% 0.21/0.46    inference(resolution,[],[f45,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0)) )),
% 0.21/0.46    inference(equality_proxy_axiom,[],[f25])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X6,X7,X5] : (sQ3_eqProxy(k1_tarski(X7),X6) | ~sQ3_eqProxy(k1_tarski(X5),X6) | ~sQ3_eqProxy(X7,X5)) )),
% 0.21/0.46    inference(resolution,[],[f37,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (sQ3_eqProxy(k1_tarski(X0),k1_tarski(X1)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.46    inference(equality_proxy_axiom,[],[f25])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~sQ3_eqProxy(X0,X1) | ~sQ3_eqProxy(X1,X2) | sQ3_eqProxy(X0,X2)) )),
% 0.21/0.46    inference(equality_proxy_axiom,[],[f25])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ~sQ3_eqProxy(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f14,f25])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ~sQ3_eqProxy(k1_tarski(sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.46    inference(resolution,[],[f55,f35])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X7] : (~sQ3_eqProxy(sK1,X7) | ~sQ3_eqProxy(k1_tarski(X7),k4_xboole_0(k2_tarski(sK0,sK1),sK2))) )),
% 0.21/0.46    inference(resolution,[],[f48,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ~sQ3_eqProxy(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k1_tarski(sK1))),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f13,f25])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ~sQ3_eqProxy(k1_xboole_0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f11,f25])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (19578)------------------------------
% 0.21/0.46  % (19578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (19578)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (19578)Memory used [KB]: 6140
% 0.21/0.46  % (19578)Time elapsed: 0.057 s
% 0.21/0.46  % (19578)------------------------------
% 0.21/0.46  % (19578)------------------------------
% 0.21/0.46  % (19572)Success in time 0.103 s
%------------------------------------------------------------------------------
