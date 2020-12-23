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
% DateTime   : Thu Dec  3 12:45:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 101 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  190 ( 516 expanded)
%              Number of equality atoms :   50 ( 120 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f165,f81])).

fof(f81,plain,(
    r1_tarski(sK1,sK4(sK0,sK5(sK1,k1_setfam_1(sK0)))) ),
    inference(resolution,[],[f75,f21])).

fof(f21,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | r1_tarski(sK1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(sK1,k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & ! [X2] :
        ( r1_tarski(sK1,X2)
        | ~ r2_hidden(X2,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X1,k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & ! [X2] :
            ( r1_tarski(X1,X2)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_tarski(sK1,k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & ! [X2] :
          ( r1_tarski(sK1,X2)
          | ~ r2_hidden(X2,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X1,X2) )
       => ( r1_tarski(X1,k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f75,plain,(
    r2_hidden(sK4(sK0,sK5(sK1,k1_setfam_1(sK0))),sK0) ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,
    ( r2_hidden(sK4(sK0,sK5(sK1,k1_setfam_1(sK0))),sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f43,f40])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK4(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK4(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f15,f14,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK2(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f43,plain,(
    ~ r2_hidden(sK5(sK1,k1_setfam_1(sK0)),k1_setfam_1(sK0)) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f23,plain,(
    ~ r1_tarski(sK1,k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f165,plain,(
    ~ r1_tarski(sK1,sK4(sK0,sK5(sK1,k1_setfam_1(sK0)))) ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,k1_setfam_1(sK0)),X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    r2_hidden(sK5(sK1,k1_setfam_1(sK0)),sK1) ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ~ r2_hidden(sK5(sK1,k1_setfam_1(sK0)),sK4(sK0,sK5(sK1,k1_setfam_1(sK0)))) ),
    inference(subsumption_resolution,[],[f69,f22])).

fof(f69,plain,
    ( ~ r2_hidden(sK5(sK1,k1_setfam_1(sK0)),sK4(sK0,sK5(sK1,k1_setfam_1(sK0))))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK4(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK4(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:10:06 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.23/0.49  % (17843)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.50  % (17843)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % (17835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f171,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(subsumption_resolution,[],[f165,f81])).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    r1_tarski(sK1,sK4(sK0,sK5(sK1,k1_setfam_1(sK0))))),
% 0.23/0.50    inference(resolution,[],[f75,f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ( ! [X2] : (~r2_hidden(X2,sK0) | r1_tarski(sK1,X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    ~r1_tarski(sK1,k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & ! [X2] : (r1_tarski(sK1,X2) | ~r2_hidden(X2,sK0))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.23/0.50  fof(f9,plain,(
% 0.23/0.50    ? [X0,X1] : (~r1_tarski(X1,k1_setfam_1(X0)) & k1_xboole_0 != X0 & ! [X2] : (r1_tarski(X1,X2) | ~r2_hidden(X2,X0))) => (~r1_tarski(sK1,k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & ! [X2] : (r1_tarski(sK1,X2) | ~r2_hidden(X2,sK0)))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f6,plain,(
% 0.23/0.50    ? [X0,X1] : (~r1_tarski(X1,k1_setfam_1(X0)) & k1_xboole_0 != X0 & ! [X2] : (r1_tarski(X1,X2) | ~r2_hidden(X2,X0)))),
% 0.23/0.50    inference(flattening,[],[f5])).
% 0.23/0.50  fof(f5,plain,(
% 0.23/0.50    ? [X0,X1] : ((~r1_tarski(X1,k1_setfam_1(X0)) & k1_xboole_0 != X0) & ! [X2] : (r1_tarski(X1,X2) | ~r2_hidden(X2,X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.23/0.50    inference(negated_conjecture,[],[f3])).
% 0.23/0.50  fof(f3,conjecture,(
% 0.23/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    r2_hidden(sK4(sK0,sK5(sK1,k1_setfam_1(sK0))),sK0)),
% 0.23/0.50    inference(subsumption_resolution,[],[f68,f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    k1_xboole_0 != sK0),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f68,plain,(
% 0.23/0.50    r2_hidden(sK4(sK0,sK5(sK1,k1_setfam_1(sK0))),sK0) | k1_xboole_0 = sK0),
% 0.23/0.50    inference(resolution,[],[f43,f40])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | r2_hidden(sK4(X0,X5),X0) | k1_xboole_0 = X0) )),
% 0.23/0.50    inference(equality_resolution,[],[f25])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK4(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f15,f14,f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK2(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X3] : (~r2_hidden(sK2(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0)))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.23/0.50    inference(rectify,[],[f11])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,plain,(
% 0.23/0.50    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ~r2_hidden(sK5(sK1,k1_setfam_1(sK0)),k1_setfam_1(sK0))),
% 0.23/0.50    inference(resolution,[],[f23,f34])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.50    inference(rectify,[],[f17])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.50    inference(nnf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,plain,(
% 0.23/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ~r1_tarski(sK1,k1_setfam_1(sK0))),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f165,plain,(
% 0.23/0.50    ~r1_tarski(sK1,sK4(sK0,sK5(sK1,k1_setfam_1(sK0))))),
% 0.23/0.50    inference(resolution,[],[f76,f59])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    ( ! [X0] : (r2_hidden(sK5(sK1,k1_setfam_1(sK0)),X0) | ~r1_tarski(sK1,X0)) )),
% 0.23/0.50    inference(resolution,[],[f42,f32])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    r2_hidden(sK5(sK1,k1_setfam_1(sK0)),sK1)),
% 0.23/0.50    inference(resolution,[],[f23,f33])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f76,plain,(
% 0.23/0.50    ~r2_hidden(sK5(sK1,k1_setfam_1(sK0)),sK4(sK0,sK5(sK1,k1_setfam_1(sK0))))),
% 0.23/0.50    inference(subsumption_resolution,[],[f69,f22])).
% 0.23/0.50  fof(f69,plain,(
% 0.23/0.50    ~r2_hidden(sK5(sK1,k1_setfam_1(sK0)),sK4(sK0,sK5(sK1,k1_setfam_1(sK0)))) | k1_xboole_0 = sK0),
% 0.23/0.50    inference(resolution,[],[f43,f39])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X5,sK4(X0,X5)) | k1_xboole_0 = X0) )),
% 0.23/0.50    inference(equality_resolution,[],[f26])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK4(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f16])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (17843)------------------------------
% 0.23/0.50  % (17843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (17843)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (17843)Memory used [KB]: 1791
% 0.23/0.50  % (17843)Time elapsed: 0.061 s
% 0.23/0.50  % (17843)------------------------------
% 0.23/0.50  % (17843)------------------------------
% 0.23/0.50  % (17819)Success in time 0.122 s
%------------------------------------------------------------------------------
