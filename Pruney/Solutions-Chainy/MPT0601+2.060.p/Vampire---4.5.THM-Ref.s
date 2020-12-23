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
% DateTime   : Thu Dec  3 12:51:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 181 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  204 ( 681 expanded)
%              Number of equality atoms :   35 ( 156 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f55,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f55,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f50,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f108,plain,(
    r2_hidden(sK4(sK1,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f107,f99])).

fof(f99,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f36,f98])).

fof(f98,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f35,f95])).

fof(f95,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X4) ) ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f41,f56])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k11_relat_1(sK1,X3))
      | r2_hidden(X3,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(k11_relat_1(sK1,X0))),sK1)
      | ~ r2_hidden(X1,k11_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f30])).

fof(f30,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
      | r2_hidden(k4_tarski(X1,X0),sK1) ) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f35,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f105,f34])).

fof(f105,plain,
    ( r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) ),
    inference(subsumption_resolution,[],[f61,f99])).

fof(f61,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:09:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (7902)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.45  % (7902)Refutation not found, incomplete strategy% (7902)------------------------------
% 0.19/0.45  % (7902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (7902)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (7902)Memory used [KB]: 10746
% 0.19/0.45  % (7902)Time elapsed: 0.070 s
% 0.19/0.45  % (7902)------------------------------
% 0.19/0.45  % (7902)------------------------------
% 0.19/0.47  % (7894)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.47  % (7894)Refutation not found, incomplete strategy% (7894)------------------------------
% 0.19/0.47  % (7894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (7894)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (7894)Memory used [KB]: 10618
% 0.19/0.47  % (7894)Time elapsed: 0.079 s
% 0.19/0.47  % (7894)------------------------------
% 0.19/0.47  % (7894)------------------------------
% 0.19/0.50  % (7893)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (7910)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.52  % (7895)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (7897)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (7917)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (7897)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f109,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(subsumption_resolution,[],[f108,f56])).
% 0.19/0.53  fof(f56,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(forward_demodulation,[],[f55,f43])).
% 0.19/0.53  fof(f43,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.19/0.53    inference(resolution,[],[f50,f46])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f32])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,plain,(
% 0.19/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.53    inference(rectify,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.53  fof(f108,plain,(
% 0.19/0.53    r2_hidden(sK4(sK1,sK0),k1_xboole_0)),
% 0.19/0.53    inference(forward_demodulation,[],[f107,f99])).
% 0.19/0.53  fof(f99,plain,(
% 0.19/0.53    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.19/0.53    inference(subsumption_resolution,[],[f36,f98])).
% 0.19/0.53  fof(f98,plain,(
% 0.19/0.53    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.19/0.53    inference(subsumption_resolution,[],[f35,f95])).
% 0.19/0.53  fof(f95,plain,(
% 0.19/0.53    ( ! [X4] : (r2_hidden(X4,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X4)) )),
% 0.19/0.53    inference(resolution,[],[f92,f65])).
% 0.19/0.53  fof(f65,plain,(
% 0.19/0.53    ( ! [X0] : (r2_hidden(sK5(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(resolution,[],[f41,f56])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.19/0.53    inference(nnf_transformation,[],[f12])).
% 0.19/0.53  fof(f12,plain,(
% 0.19/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k11_relat_1(sK1,X3)) | r2_hidden(X3,k1_relat_1(sK1))) )),
% 0.19/0.53    inference(resolution,[],[f63,f51])).
% 0.19/0.53  fof(f51,plain,(
% 0.19/0.53    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.19/0.53    inference(equality_resolution,[],[f38])).
% 0.19/0.53  fof(f38,plain,(
% 0.19/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.19/0.53    inference(rectify,[],[f20])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.19/0.53  fof(f63,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK6(k11_relat_1(sK1,X0))),sK1) | ~r2_hidden(X1,k11_relat_1(sK1,X0))) )),
% 0.19/0.53    inference(resolution,[],[f62,f47])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(sK6(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f31])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f14,plain,(
% 0.19/0.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK1,X1)) | r2_hidden(k4_tarski(X1,X0),sK1)) )),
% 0.19/0.53    inference(resolution,[],[f45,f34])).
% 0.19/0.53  fof(f34,plain,(
% 0.19/0.53    v1_relat_1(sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f19])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.19/0.53    inference(flattening,[],[f16])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,plain,(
% 0.19/0.53    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.19/0.53    inference(negated_conjecture,[],[f8])).
% 0.19/0.53  fof(f8,conjecture,(
% 0.19/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.19/0.53    inference(nnf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.19/0.53    inference(ennf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f19])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ~r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f19])).
% 0.19/0.53  fof(f107,plain,(
% 0.19/0.53    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.19/0.53    inference(subsumption_resolution,[],[f105,f34])).
% 0.19/0.53  fof(f105,plain,(
% 0.19/0.53    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.19/0.53    inference(resolution,[],[f100,f44])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f29])).
% 0.19/0.53  fof(f100,plain,(
% 0.19/0.53    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)),
% 0.19/0.53    inference(subsumption_resolution,[],[f61,f99])).
% 0.19/0.53  fof(f61,plain,(
% 0.19/0.53    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)),
% 0.19/0.53    inference(resolution,[],[f52,f35])).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f25])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (7897)------------------------------
% 0.19/0.53  % (7897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (7897)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (7897)Memory used [KB]: 6268
% 0.19/0.53  % (7897)Time elapsed: 0.130 s
% 0.19/0.53  % (7897)------------------------------
% 0.19/0.53  % (7897)------------------------------
% 0.19/0.53  % (7891)Success in time 0.178 s
%------------------------------------------------------------------------------
