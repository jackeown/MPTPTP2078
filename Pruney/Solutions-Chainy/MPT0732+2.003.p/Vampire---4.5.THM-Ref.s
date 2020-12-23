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
% DateTime   : Thu Dec  3 12:55:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 241 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f18,f20,f145,f22])).

% (19200)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f145,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f144,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k3_xboole_0(X0,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f23,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f144,plain,(
    ! [X2] : ~ sQ4_eqProxy(k3_xboole_0(X2,sK2),sK1) ),
    inference(resolution,[],[f142,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f33])).

fof(f142,plain,(
    ! [X0] : ~ sQ4_eqProxy(sK1,k3_xboole_0(X0,sK2)) ),
    inference(subsumption_resolution,[],[f136,f43])).

fof(f43,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f33])).

fof(f136,plain,(
    ! [X0] :
      ( ~ sQ4_eqProxy(sK0,sK0)
      | ~ sQ4_eqProxy(sK1,k3_xboole_0(X0,sK2)) ) ),
    inference(resolution,[],[f108,f19])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK0,sK1)
    & v1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1)
        & v1_ordinal1(X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK0,sK1)
      & v1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_ordinal1(X2)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X1) )
         => r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sQ4_eqProxy(X0,sK0)
      | ~ sQ4_eqProxy(X1,k3_xboole_0(X2,sK2)) ) ),
    inference(resolution,[],[f50,f21])).

fof(f21,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X7)
      | ~ sQ4_eqProxy(X10,X11)
      | ~ sQ4_eqProxy(X7,k3_xboole_0(X8,X9)) ) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f33])).

fof(f20,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (19201)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (19202)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (19203)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (19209)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (19211)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (19201)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f18,f20,f145,f22])).
% 0.22/0.51  % (19200)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~r1_tarski(sK1,sK2)),
% 0.22/0.51    inference(resolution,[],[f144,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sQ4_eqProxy(k3_xboole_0(X0,X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(equality_proxy_replacement,[],[f23,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X2] : (~sQ4_eqProxy(k3_xboole_0(X2,sK2),sK1)) )),
% 0.22/0.51    inference(resolution,[],[f142,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.22/0.51    inference(equality_proxy_axiom,[],[f33])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X0] : (~sQ4_eqProxy(sK1,k3_xboole_0(X0,sK2))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.22/0.51    inference(equality_proxy_axiom,[],[f33])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0] : (~sQ4_eqProxy(sK0,sK0) | ~sQ4_eqProxy(sK1,k3_xboole_0(X0,sK2))) )),
% 0.22/0.51    inference(resolution,[],[f108,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    r2_hidden(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r2_hidden(sK0,sK1) & v1_ordinal1(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r2_hidden(X0,X1) & v1_ordinal1(X2)) => (~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r2_hidden(sK0,sK1) & v1_ordinal1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r2_hidden(X0,X1) & v1_ordinal1(X2))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((~r2_hidden(X0,X2) & (r2_hidden(X1,X2) & r2_hidden(X0,X1))) & v1_ordinal1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (v1_ordinal1(X2) => ((r2_hidden(X1,X2) & r2_hidden(X0,X1)) => r2_hidden(X0,X2)))),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_ordinal1(X2) => ((r2_hidden(X1,X2) & r2_hidden(X0,X1)) => r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~sQ4_eqProxy(X0,sK0) | ~sQ4_eqProxy(X1,k3_xboole_0(X2,sK2))) )),
% 0.22/0.51    inference(resolution,[],[f50,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X10,X8,X7,X11,X9] : (r2_hidden(X11,X9) | ~r2_hidden(X10,X7) | ~sQ4_eqProxy(X10,X11) | ~sQ4_eqProxy(X7,k3_xboole_0(X8,X9))) )),
% 0.22/0.51    inference(resolution,[],[f40,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(rectify,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~sQ4_eqProxy(X2,X3) | ~r2_hidden(X0,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.22/0.51    inference(equality_proxy_axiom,[],[f33])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    r2_hidden(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    v1_ordinal1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (19201)------------------------------
% 0.22/0.51  % (19201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19201)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (19201)Memory used [KB]: 6140
% 0.22/0.51  % (19201)Time elapsed: 0.073 s
% 0.22/0.51  % (19201)------------------------------
% 0.22/0.51  % (19201)------------------------------
% 0.22/0.51  % (19195)Success in time 0.152 s
%------------------------------------------------------------------------------
