%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  71 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 ( 228 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f124,f124,f182,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | sQ3_eqProxy(k3_tarski(X0),X1)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f21,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK0(X0,X1),X3) )
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( ( r2_hidden(sK1(X0,X1),X0)
              & r2_hidden(sK0(X0,X1),sK1(X0,X1)) )
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK2(X0,X5),X0)
                & r2_hidden(X5,sK2(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK0(X0,X1),X3) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK0(X0,X1),X4) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK0(X0,X1),X4) )
     => ( r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK2(X0,X5),X0)
        & r2_hidden(X5,sK2(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f182,plain,(
    ~ sQ3_eqProxy(k3_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f167,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f167,plain,(
    ~ sQ3_eqProxy(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f163,f32])).

fof(f32,plain,(
    ! [X0] : sQ3_eqProxy(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(equality_proxy_replacement,[],[f16,f30])).

fof(f16,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f163,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(X0,k1_xboole_0)
      | ~ sQ3_eqProxy(X0,k3_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0))) ) ),
    inference(resolution,[],[f155,f32])).

fof(f155,plain,(
    ! [X4,X5] :
      ( ~ sQ3_eqProxy(X5,k1_xboole_0)
      | ~ sQ3_eqProxy(X4,k3_tarski(X5))
      | ~ sQ3_eqProxy(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f127,f43])).

fof(f127,plain,(
    ! [X4,X5] :
      ( ~ sQ3_eqProxy(k1_xboole_0,X4)
      | ~ sQ3_eqProxy(X4,k3_tarski(X5))
      | ~ sQ3_eqProxy(X5,k1_xboole_0) ) ),
    inference(resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(k1_xboole_0,X0)
      | ~ sQ3_eqProxy(X1,k3_tarski(X0))
      | ~ sQ3_eqProxy(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f65,plain,(
    ! [X2] :
      ( ~ sQ3_eqProxy(k1_xboole_0,k3_tarski(X2))
      | ~ sQ3_eqProxy(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X3] :
      ( ~ sQ3_eqProxy(k3_tarski(X3),k1_xboole_0)
      | ~ sQ3_eqProxy(k1_xboole_0,X3) ) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k3_tarski(X0),k3_tarski(X1))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f48,plain,(
    ! [X1] :
      ( ~ sQ3_eqProxy(k3_tarski(k1_xboole_0),X1)
      | ~ sQ3_eqProxy(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ~ sQ3_eqProxy(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,k3_tarski(k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f15,f30])).

% (4919)Refutation not found, incomplete strategy% (4919)------------------------------
% (4919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f15,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f5])).

fof(f5,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f124,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,X1)) ),
    inference(subsumption_resolution,[],[f84,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X1)) ) ),
    inference(factoring,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:24:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (4911)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (4911)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f124,f124,f182,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | sQ3_eqProxy(k3_tarski(X0),X1) | r2_hidden(sK0(X0,X1),X1)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f21,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & ((r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),sK1(X0,X1))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK0(X0,X1),X4)) | r2_hidden(sK0(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK0(X0,X1),X4)) => (r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),sK1(X0,X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.48    inference(rectify,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k3_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.21/0.48    inference(resolution,[],[f167,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f30])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.48    inference(resolution,[],[f163,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f16,f30])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ3_eqProxy(X0,k1_xboole_0) | ~sQ3_eqProxy(X0,k3_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0)))) )),
% 0.21/0.48    inference(resolution,[],[f155,f32])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~sQ3_eqProxy(X5,k1_xboole_0) | ~sQ3_eqProxy(X4,k3_tarski(X5)) | ~sQ3_eqProxy(X4,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f127,f43])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~sQ3_eqProxy(k1_xboole_0,X4) | ~sQ3_eqProxy(X4,k3_tarski(X5)) | ~sQ3_eqProxy(X5,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f66,f43])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ3_eqProxy(k1_xboole_0,X0) | ~sQ3_eqProxy(X1,k3_tarski(X0)) | ~sQ3_eqProxy(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f65,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ3_eqProxy(X0,X2) | ~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f30])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2] : (~sQ3_eqProxy(k1_xboole_0,k3_tarski(X2)) | ~sQ3_eqProxy(k1_xboole_0,X2)) )),
% 0.21/0.48    inference(resolution,[],[f55,f43])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X3] : (~sQ3_eqProxy(k3_tarski(X3),k1_xboole_0) | ~sQ3_eqProxy(k1_xboole_0,X3)) )),
% 0.21/0.48    inference(resolution,[],[f48,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k3_tarski(X0),k3_tarski(X1)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f30])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X1] : (~sQ3_eqProxy(k3_tarski(k1_xboole_0),X1) | ~sQ3_eqProxy(X1,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f44,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k3_tarski(k1_xboole_0),k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f43,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,k3_tarski(k1_xboole_0))),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f15,f30])).
% 0.21/0.48  % (4919)Refutation not found, incomplete strategy% (4919)------------------------------
% 0.21/0.48  % (4919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.48    inference(nnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X1))) )),
% 0.21/0.48    inference(factoring,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (4911)------------------------------
% 0.21/0.48  % (4911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4911)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (4911)Memory used [KB]: 6140
% 0.21/0.48  % (4911)Time elapsed: 0.059 s
% 0.21/0.48  % (4911)------------------------------
% 0.21/0.48  % (4911)------------------------------
% 0.21/0.48  % (4903)Success in time 0.121 s
%------------------------------------------------------------------------------
