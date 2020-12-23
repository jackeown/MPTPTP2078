%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 155 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f21,f20,f57,f54,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ sQ3_eqProxy(X0,k1_wellord2(sK0))
      | ~ v8_relat_2(X0)
      | ~ sQ3_eqProxy(k3_relat_1(X0),sK0) ) ),
    inference(resolution,[],[f58,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r8_relat_2(X1,X0)
      | ~ sQ3_eqProxy(X0,sK0)
      | ~ sQ3_eqProxy(X1,k1_wellord2(sK0)) ) ),
    inference(resolution,[],[f51,f19])).

fof(f19,plain,(
    ~ r8_relat_2(k1_wellord2(sK0),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ r8_relat_2(k1_wellord2(sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] : ~ r8_relat_2(k1_wellord2(X0),X0)
   => ~ r8_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r8_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r8_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r8_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord2)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r8_relat_2(X1,X3)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ r8_relat_2(X0,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f54,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f38])).

fof(f57,plain,(
    ! [X0] : sQ3_eqProxy(k3_relat_1(k1_wellord2(X0)),X0) ),
    inference(subsumption_resolution,[],[f43,f21])).

fof(f43,plain,(
    ! [X0] :
      ( sQ3_eqProxy(k3_relat_1(k1_wellord2(X0)),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_proxy_replacement,[],[f37,f38])).

fof(f37,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & r2_hidden(sK2(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f20,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14730)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (14731)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (14730)Refutation not found, incomplete strategy% (14730)------------------------------
% 0.21/0.47  % (14730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14730)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14730)Memory used [KB]: 1535
% 0.21/0.47  % (14730)Time elapsed: 0.050 s
% 0.21/0.47  % (14730)------------------------------
% 0.21/0.47  % (14730)------------------------------
% 0.21/0.48  % (14722)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (14722)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f21,f20,f57,f54,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~sQ3_eqProxy(X0,k1_wellord2(sK0)) | ~v8_relat_2(X0) | ~sQ3_eqProxy(k3_relat_1(X0),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f58,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (((v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0))) & (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : ((v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r8_relat_2(X1,X0) | ~sQ3_eqProxy(X0,sK0) | ~sQ3_eqProxy(X1,k1_wellord2(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f51,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~r8_relat_2(k1_wellord2(sK0),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~r8_relat_2(k1_wellord2(sK0),sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : ~r8_relat_2(k1_wellord2(X0),X0) => ~r8_relat_2(k1_wellord2(sK0),sK0)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : ~r8_relat_2(k1_wellord2(X0),X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : r8_relat_2(k1_wellord2(X0),X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : r8_relat_2(k1_wellord2(X0),X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord2)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r8_relat_2(X1,X3) | ~sQ3_eqProxy(X2,X3) | ~r8_relat_2(X0,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f38])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k3_relat_1(k1_wellord2(X0)),X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f43,f21])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k3_relat_1(k1_wellord2(X0)),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f37,f38])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(rectify,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0] : (v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (14722)------------------------------
% 0.21/0.48  % (14722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14722)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (14722)Memory used [KB]: 6140
% 0.21/0.48  % (14722)Time elapsed: 0.053 s
% 0.21/0.48  % (14722)------------------------------
% 0.21/0.48  % (14722)------------------------------
% 0.21/0.48  % (14716)Success in time 0.115 s
%------------------------------------------------------------------------------
