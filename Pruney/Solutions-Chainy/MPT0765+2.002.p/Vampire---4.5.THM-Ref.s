%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 179 expanded)
%              Number of leaves         :    7 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 924 expanded)
%              Number of equality atoms :   27 ( 144 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(subsumption_resolution,[],[f49,f43])).

fof(f43,plain,(
    r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f21,plain,(
    k1_xboole_0 != k3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X1] :
        ( ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
          & r2_hidden(sK1(X1),k3_relat_1(sK0)) )
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    & k1_xboole_0 != k3_relat_1(sK0)
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        & k3_relat_1(X0) != k1_xboole_0
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
              & r2_hidden(X2,k3_relat_1(sK0)) )
          | ~ r2_hidden(X1,k3_relat_1(sK0)) )
      & k1_xboole_0 != k3_relat_1(sK0)
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
          & r2_hidden(X2,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        & r2_hidden(sK1(X1),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k3_relat_1(X0))
                     => r2_hidden(k4_tarski(X1,X2),X0) )
                  & r2_hidden(X1,k3_relat_1(X0)) )
            & k3_relat_1(X0) != k1_xboole_0
            & v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,k3_relat_1(X0))
                   => r2_hidden(k4_tarski(X1,X2),X0) )
                & r2_hidden(X1,k3_relat_1(X0)) )
          & k3_relat_1(X0) != k1_xboole_0
          & v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord1)).

fof(f42,plain,
    ( k1_xboole_0 = k3_relat_1(sK0)
    | r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(sK0,X0),X0) ) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f34,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | r2_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( r2_wellord1(X0,k3_relat_1(X0))
          | ~ v2_wellord1(X0) )
        & ( v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(sK0,X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r2_hidden(sK2(sK0,X0),X0) ) ),
    inference(resolution,[],[f26,f19])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | r2_hidden(sK2(X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(k4_tarski(sK2(X1,X2),X4),X1)
                | ~ r2_hidden(X4,X2) )
            & r2_hidden(sK2(X1,X2),X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).

fof(f15,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X2) )
          & r2_hidden(X3,X2) )
     => ( ! [X4] :
            ( r2_hidden(k4_tarski(sK2(X1,X2),X4),X1)
            | ~ r2_hidden(X4,X2) )
        & r2_hidden(sK2(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

fof(f49,plain,(
    ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f48,f22])).

fof(f22,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),k3_relat_1(sK0))
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f47,f31])).

fof(f47,plain,
    ( ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f46,f21])).

fof(f46,plain,
    ( ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(resolution,[],[f45,f43])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,X0),k3_relat_1(sK0))
      | ~ r2_hidden(sK1(sK2(sK0,X0)),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f44,f23])).

fof(f23,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(sK0,X0),X1),sK0)
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f41,f35])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_wellord1(sK0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0) ) ),
    inference(resolution,[],[f27,f19])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | r2_hidden(k4_tarski(sK2(X1,X2),X4),X1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:03:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (6306)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (6314)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.50  % (6314)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f49,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f42,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    k1_xboole_0 != k3_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X1] : ((~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0)) => (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) => (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0] : ((! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)) & v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    k1_xboole_0 = k3_relat_1(sK0) | r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f40,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK0)) | k1_xboole_0 = X0 | r2_hidden(sK2(sK0,X0),X0)) )),
% 0.22/0.50    inference(resolution,[],[f39,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f34,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    r2_wellord1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f25,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    v2_wellord1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_wellord1(X0) | r2_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (((r2_wellord1(X0,k3_relat_1(X0)) | ~v2_wellord1(X0)) & (v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0] : ((r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_wellord1(sK0,X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r2_hidden(sK2(sK0,X0),X0)) )),
% 0.22/0.50    inference(resolution,[],[f26,f19])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0) | ~r2_wellord1(X1,X0) | r2_hidden(sK2(X1,X2),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((! [X4] : (r2_hidden(k4_tarski(sK2(X1,X2),X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(sK2(X1,X2),X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X2,X1] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) => (! [X4] : (r2_hidden(k4_tarski(sK2(X1,X2),X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(sK2(X1,X2),X2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1] : ((! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_wellord1(X1,X0) => ! [X2] : ~(! [X3] : ~(! [X4] : (r2_hidden(X4,X2) => r2_hidden(k4_tarski(X3,X4),X1)) & r2_hidden(X3,X2)) & k1_xboole_0 != X2 & r1_tarski(X2,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f48,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(sK1(X1),k3_relat_1(sK0)) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f47,f31])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f46,f21])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f45,f43])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK2(sK0,X0)),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f44,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(sK0,X0),X1),sK0) | ~r1_tarski(X0,k3_relat_1(sK0)) | ~r2_hidden(X1,X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(resolution,[],[f41,f35])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_wellord1(sK0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0)) )),
% 0.22/0.50    inference(resolution,[],[f27,f19])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X4,X2) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0) | ~r2_wellord1(X1,X0) | r2_hidden(k4_tarski(sK2(X1,X2),X4),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (6314)------------------------------
% 0.22/0.50  % (6314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6314)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (6314)Memory used [KB]: 1663
% 0.22/0.50  % (6314)Time elapsed: 0.074 s
% 0.22/0.50  % (6314)------------------------------
% 0.22/0.50  % (6314)------------------------------
% 0.22/0.50  % (6297)Success in time 0.129 s
%------------------------------------------------------------------------------
