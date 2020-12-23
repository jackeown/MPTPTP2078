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
% DateTime   : Thu Dec  3 12:41:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  92 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 318 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f55])).

fof(f55,plain,(
    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) ),
    inference(resolution,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f28,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f101,plain,(
    ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f100,f86])).

fof(f86,plain,(
    ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0) ),
    inference(superposition,[],[f64,f81])).

fof(f81,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f79,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f35,f59])).

fof(f59,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f44,f52])).

fof(f52,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f27,f43])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f64,plain,(
    ! [X0] : ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f100,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0)
    | ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) ),
    inference(resolution,[],[f61,f74])).

fof(f74,plain,(
    ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1) ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f56,plain,(
    ~ r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f49,f52])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (31402)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.48  % (31410)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.49  % (31402)Refutation not found, incomplete strategy% (31402)------------------------------
% 0.19/0.49  % (31402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (31402)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (31402)Memory used [KB]: 10746
% 0.19/0.49  % (31402)Time elapsed: 0.093 s
% 0.19/0.49  % (31402)------------------------------
% 0.19/0.49  % (31402)------------------------------
% 0.19/0.49  % (31418)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (31410)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (31396)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.50  % (31406)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.50  % (31414)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (31419)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f102,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f101,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)),
% 0.19/0.50    inference(resolution,[],[f28,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) & r1_tarski(sK0,sK1)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1)) => (~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) & r1_tarski(sK0,sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.50    inference(negated_conjecture,[],[f10])).
% 0.19/0.50  fof(f10,conjecture,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.19/0.50  fof(f101,plain,(
% 0.19/0.50    ~r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f100,f86])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    ~r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0)),
% 0.19/0.50    inference(superposition,[],[f64,f81])).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 0.19/0.50    inference(resolution,[],[f79,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.50    inference(nnf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.19/0.50    inference(superposition,[],[f35,f59])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.19/0.50    inference(superposition,[],[f44,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.19/0.50    inference(resolution,[],[f27,f43])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    r1_tarski(sK0,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(X0,sK0))) )),
% 0.19/0.50    inference(resolution,[],[f55,f50])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.19/0.50    inference(equality_resolution,[],[f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.50    inference(rectify,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.50    inference(flattening,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.50    inference(nnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.19/0.50  fof(f100,plain,(
% 0.19/0.50    r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0) | ~r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)),
% 0.19/0.50    inference(resolution,[],[f61,f74])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    ~r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1)),
% 0.19/0.50    inference(resolution,[],[f56,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ~r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))),
% 0.19/0.50    inference(resolution,[],[f28,f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0)) )),
% 0.19/0.50    inference(superposition,[],[f49,f52])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.19/0.50    inference(equality_resolution,[],[f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (31410)------------------------------
% 0.19/0.50  % (31410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (31410)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (31410)Memory used [KB]: 1791
% 0.19/0.50  % (31410)Time elapsed: 0.110 s
% 0.19/0.50  % (31410)------------------------------
% 0.19/0.50  % (31410)------------------------------
% 0.19/0.51  % (31391)Success in time 0.153 s
%------------------------------------------------------------------------------
