%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 112 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 461 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f117,f61])).

fof(f61,plain,(
    r2_hidden(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) ),
    inference(forward_demodulation,[],[f58,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f58,plain,(
    r2_hidden(k2_xboole_0(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0)))),k2_setfam_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f45,f45,f40])).

fof(f40,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k2_xboole_0(X9,X10),k2_setfam_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k2_xboole_0(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k2_xboole_0(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k2_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k2_xboole_0(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k2_xboole_0(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k2_xboole_0(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k2_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k2_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k2_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

fof(f45,plain,(
    r2_hidden(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f25,f44,f27])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(sK2(X1,X4),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK1(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK2(X1,X4))
              & r2_hidden(sK2(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f16,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK1(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK2(X1,X4))
        & r2_hidden(sK2(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f44,plain,(
    r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).

fof(f11,plain,
    ( ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0))
   => ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

fof(f25,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_setfam_1(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).

fof(f117,plain,(
    ~ r2_hidden(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f46,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK1(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    r1_tarski(sK1(sK0,k2_setfam_1(sK0,sK0)),sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0)))) ),
    inference(unit_resulting_resolution,[],[f25,f44,f28])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r1_tarski(X4,sK2(X1,X4))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:45:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (7307)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (7299)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (7307)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f117,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    r2_hidden(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))),
% 0.22/0.48    inference(forward_demodulation,[],[f58,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    inference(rectify,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    r2_hidden(k2_xboole_0(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0)))),k2_setfam_1(sK0,sK0))),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f45,f45,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X10,X1,X9] : (r2_hidden(k2_xboole_0(X9,X10),k2_setfam_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k2_xboole_0(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_setfam_1(X0,X1) != X2) )),
% 0.22/0.48    inference(equality_resolution,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_setfam_1(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k2_setfam_1(X0,X1) = X2 | ((! [X4,X5] : (k2_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_setfam_1(X0,X1) != X2))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f19,f22,f21,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k2_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k2_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k2_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X7,X6] : (k2_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k2_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X8,X1,X0] : (? [X11,X12] : (k2_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k2_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k2_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k2_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k2_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k2_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_setfam_1(X0,X1) != X2))),
% 0.22/0.48    inference(rectify,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k2_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_setfam_1(X0,X1) != X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    r2_hidden(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f25,f44,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(sK2(X1,X4),X1) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK1(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK2(X1,X4)) & r2_hidden(sK2(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f16,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK1(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK2(X1,X4)) & r2_hidden(sK2(X1,X4),X1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f24,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ~r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ~r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0)) => ~r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0] : (r1_setfam_1(X0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0] : r1_setfam_1(X0,X0)),
% 0.22/0.48    inference(rectify,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_setfam_1(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~r2_hidden(sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f24,f46,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~r1_tarski(sK1(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    r1_tarski(sK1(sK0,k2_setfam_1(sK0,sK0)),sK2(sK0,sK1(sK0,k2_setfam_1(sK0,sK0))))),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f25,f44,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r1_tarski(X4,sK2(X1,X4)) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7307)------------------------------
% 0.22/0.48  % (7307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7307)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7307)Memory used [KB]: 6140
% 0.22/0.48  % (7307)Time elapsed: 0.012 s
% 0.22/0.48  % (7307)------------------------------
% 0.22/0.48  % (7307)------------------------------
% 0.22/0.48  % (7291)Success in time 0.121 s
%------------------------------------------------------------------------------
