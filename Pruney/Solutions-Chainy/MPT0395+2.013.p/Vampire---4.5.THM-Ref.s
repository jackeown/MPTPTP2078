%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  64 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 217 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f21,f56,f38,f189])).

fof(f189,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK0,X3)
      | ~ sQ4_eqProxy(X2,sK2(sK0,sK1))
      | r2_hidden(X2,k3_xboole_0(sK0,X3)) ) ),
    inference(resolution,[],[f177,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k3_xboole_0(X0,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f25,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f177,plain,(
    ! [X4,X5] :
      ( ~ sQ4_eqProxy(X5,sK0)
      | r2_hidden(X4,X5)
      | ~ sQ4_eqProxy(X4,sK2(sK0,sK1)) ) ),
    inference(resolution,[],[f167,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f167,plain,(
    ! [X4,X5] :
      ( ~ sQ4_eqProxy(sK2(sK0,sK1),X4)
      | r2_hidden(X4,X5)
      | ~ sQ4_eqProxy(X5,sK0) ) ),
    inference(resolution,[],[f162,f51])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(sK0,X1)
      | r2_hidden(X0,X1)
      | ~ sQ4_eqProxy(sK2(sK0,sK1),X0) ) ),
    inference(resolution,[],[f101,f22])).

fof(f22,plain,(
    ~ r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_setfam_1(X0,X2)
      | ~ sQ4_eqProxy(sK2(X0,X2),X3)
      | r2_hidden(X3,X1)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f38,plain,(
    ! [X0] : sQ4_eqProxy(k2_xboole_0(X0,k1_xboole_0),X0) ),
    inference(equality_proxy_replacement,[],[f23,f37])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f56,plain,(
    ! [X2,X3] : ~ r2_hidden(k2_xboole_0(sK2(sK0,sK1),X2),k3_xboole_0(X3,sK1)) ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f54,plain,(
    ! [X0] : ~ r2_hidden(k2_xboole_0(sK2(sK0,sK1),X0),sK1) ),
    inference(resolution,[],[f53,f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r2_hidden(k2_xboole_0(sK2(X0,X1),X2),X1) ) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (25035)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (25027)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (25038)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (25027)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f21,f56,f38,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r1_tarski(sK0,X3) | ~sQ4_eqProxy(X2,sK2(sK0,sK1)) | r2_hidden(X2,k3_xboole_0(sK0,X3))) )),
% 0.21/0.48    inference(resolution,[],[f177,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ4_eqProxy(k3_xboole_0(X0,X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f25,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~sQ4_eqProxy(X5,sK0) | r2_hidden(X4,X5) | ~sQ4_eqProxy(X4,sK2(sK0,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f167,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~sQ4_eqProxy(sK2(sK0,sK1),X4) | r2_hidden(X4,X5) | ~sQ4_eqProxy(X5,sK0)) )),
% 0.21/0.48    inference(resolution,[],[f162,f51])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ4_eqProxy(sK0,X1) | r2_hidden(X0,X1) | ~sQ4_eqProxy(sK2(sK0,sK1),X0)) )),
% 0.21/0.48    inference(resolution,[],[f101,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~r1_setfam_1(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1)) => (~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r1_setfam_1(X0,X2) | ~sQ4_eqProxy(sK2(X0,X2),X3) | r2_hidden(X3,X1) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f47,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~sQ4_eqProxy(X2,X3) | ~sQ4_eqProxy(X0,X1) | r2_hidden(X1,X3)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (sQ4_eqProxy(k2_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f23,f37])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(k2_xboole_0(sK2(sK0,sK1),X2),k3_xboole_0(X3,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f54,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(rectify,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k2_xboole_0(sK2(sK0,sK1),X0),sK1)) )),
% 0.21/0.48    inference(resolution,[],[f53,f22])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_setfam_1(X0,X1) | ~r2_hidden(k2_xboole_0(sK2(X0,X1),X2),X1)) )),
% 0.21/0.48    inference(resolution,[],[f27,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r1_tarski(sK2(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (25027)------------------------------
% 0.21/0.48  % (25027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25027)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (25027)Memory used [KB]: 6268
% 0.21/0.48  % (25027)Time elapsed: 0.057 s
% 0.21/0.48  % (25027)------------------------------
% 0.21/0.48  % (25027)------------------------------
% 0.21/0.48  % (25020)Success in time 0.112 s
%------------------------------------------------------------------------------
