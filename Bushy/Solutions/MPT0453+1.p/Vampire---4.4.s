%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t39_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:02 EDT 2019

% Result     : Theorem 100.24s
% Output     : Refutation 100.24s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 625 expanded)
%              Number of leaves         :   14 ( 181 expanded)
%              Depth                    :   19
%              Number of atoms          :  432 (2312 expanded)
%              Number of equality atoms :   58 ( 495 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13645,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13644,f10236])).

fof(f10236,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f10183,f73])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',idempotence_k3_xboole_0)).

fof(f10183,plain,(
    ! [X2,X3] : v1_relat_1(k3_xboole_0(k3_xboole_0(X2,sK0),X3)) ),
    inference(subsumption_resolution,[],[f10175,f56])).

fof(f56,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)) != k4_relat_1(k3_xboole_0(sK0,sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k3_xboole_0(k4_relat_1(sK0),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(sK0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(X0,X1))
          & v1_relat_1(X1) )
     => ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(sK1)) != k4_relat_1(k3_xboole_0(X0,sK1))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k3_xboole_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',t39_relat_1)).

fof(f10175,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k3_xboole_0(k3_xboole_0(X2,sK0),X3))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f10127,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',fc1_relat_1)).

fof(f10127,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k3_xboole_0(sK0,X2))
      | v1_relat_1(k3_xboole_0(k3_xboole_0(X2,sK0),X3)) ) ),
    inference(resolution,[],[f10055,f75])).

fof(f10055,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k3_xboole_0(k3_xboole_0(sK0,X0),X1))
      | v1_relat_1(k3_xboole_0(k3_xboole_0(X0,sK0),X1)) ) ),
    inference(resolution,[],[f6434,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',dt_k4_relat_1)).

fof(f6434,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(k3_xboole_0(sK0,X1),X2)))
      | v1_relat_1(k3_xboole_0(k3_xboole_0(X1,sK0),X2)) ) ),
    inference(superposition,[],[f4212,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',commutativity_k3_xboole_0)).

fof(f4212,plain,(
    ! [X24,X23] :
      ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(k3_xboole_0(X23,sK0),X24)))
      | v1_relat_1(k3_xboole_0(k3_xboole_0(X23,sK0),X24)) ) ),
    inference(superposition,[],[f62,f1385])).

fof(f1385,plain,(
    ! [X14,X13] : k3_xboole_0(k3_xboole_0(X13,sK0),X14) = k4_relat_1(k4_relat_1(k3_xboole_0(k3_xboole_0(X13,sK0),X14))) ),
    inference(resolution,[],[f315,f56])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k3_xboole_0(X0,X1),X2) = k4_relat_1(k4_relat_1(k3_xboole_0(k3_xboole_0(X0,X1),X2))) ) ),
    inference(resolution,[],[f110,f119])).

fof(f119,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k3_xboole_0(X2,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f75,f74])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,X1) = k4_relat_1(k4_relat_1(k3_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f63,f75])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',involutiveness_k4_relat_1)).

fof(f13644,plain,(
    ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f13638,f62])).

fof(f13638,plain,(
    ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f13636,f2493])).

fof(f2493,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f2492,f73])).

fof(f2492,plain,(
    v1_relat_1(k3_xboole_0(k4_relat_1(sK1),k4_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f2491,f57])).

fof(f57,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f2491,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k3_xboole_0(k4_relat_1(sK1),k4_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f2484,f114])).

fof(f114,plain,(
    k4_relat_1(k4_relat_1(sK1)) = sK1 ),
    inference(resolution,[],[f63,f57])).

fof(f2484,plain,
    ( ~ v1_relat_1(k4_relat_1(k4_relat_1(sK1)))
    | v1_relat_1(k3_xboole_0(k4_relat_1(sK1),k4_relat_1(sK1))) ),
    inference(superposition,[],[f1353,f73])).

fof(f1353,plain,(
    ! [X13] :
      ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(k4_relat_1(sK1),X13)))
      | v1_relat_1(k3_xboole_0(k4_relat_1(sK1),X13)) ) ),
    inference(superposition,[],[f62,f1308])).

fof(f1308,plain,(
    ! [X10] : k3_xboole_0(k4_relat_1(sK1),X10) = k4_relat_1(k4_relat_1(k3_xboole_0(k4_relat_1(sK1),X10))) ),
    inference(resolution,[],[f317,f57])).

fof(f317,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | k3_xboole_0(k4_relat_1(X6),X7) = k4_relat_1(k4_relat_1(k3_xboole_0(k4_relat_1(X6),X7))) ) ),
    inference(resolution,[],[f110,f62])).

fof(f13636,plain,
    ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f13635,f119])).

fof(f13635,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f13634,f13175])).

fof(f13175,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f13172,f1901])).

fof(f1901,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X3,X2),sK0) ) ),
    inference(resolution,[],[f1835,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k4_relat_1(sK0))
      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),sK0) ) ),
    inference(superposition,[],[f97,f113])).

fof(f113,plain,(
    k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(resolution,[],[f63,f56])).

fof(f97,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f90,f62])).

fof(f90,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',d7_relat_1)).

fof(f1835,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f1834,f73])).

fof(f1834,plain,(
    v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f1833,f56])).

fof(f1833,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f1826,f113])).

fof(f1826,plain,
    ( ~ v1_relat_1(k4_relat_1(k4_relat_1(sK0)))
    | v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0))) ),
    inference(superposition,[],[f1336,f73])).

fof(f1336,plain,(
    ! [X13] :
      ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(k4_relat_1(sK0),X13)))
      | v1_relat_1(k3_xboole_0(k4_relat_1(sK0),X13)) ) ),
    inference(superposition,[],[f62,f1307])).

fof(f1307,plain,(
    ! [X9] : k3_xboole_0(k4_relat_1(sK0),X9) = k4_relat_1(k4_relat_1(k3_xboole_0(k4_relat_1(sK0),X9))) ),
    inference(resolution,[],[f317,f56])).

fof(f13172,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),sK0) ),
    inference(resolution,[],[f1183,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',d4_xboole_0)).

fof(f1183,plain,
    ( r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1180,f329])).

fof(f329,plain,(
    ! [X6] :
      ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,X6)))
      | v1_relat_1(k3_xboole_0(sK0,X6)) ) ),
    inference(superposition,[],[f62,f319])).

fof(f319,plain,(
    ! [X9] : k3_xboole_0(sK0,X9) = k4_relat_1(k4_relat_1(k3_xboole_0(sK0,X9))) ),
    inference(resolution,[],[f110,f56])).

fof(f1180,plain,
    ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f265,f97])).

fof(f265,plain,
    ( r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0)) ),
    inference(resolution,[],[f233,f93])).

fof(f233,plain,
    ( r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1))) ),
    inference(extensionality_resolution,[],[f66,f58])).

fof(f58,plain,(
    k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)) != k4_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t39_relat_1.p',d2_relat_1)).

fof(f13634,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f13633,f13249])).

fof(f13249,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f13247,f2536])).

fof(f2536,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X3,X2),sK1) ) ),
    inference(resolution,[],[f2493,f187])).

fof(f187,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k4_relat_1(sK1))
      | r2_hidden(k4_tarski(X3,X2),k4_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(superposition,[],[f97,f114])).

fof(f13247,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),sK1) ),
    inference(resolution,[],[f1226,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1226,plain,
    ( r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1223,f329])).

fof(f1223,plain,
    ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f266,f97])).

fof(f266,plain,
    ( r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1)) ),
    inference(resolution,[],[f233,f92])).

fof(f13633,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f13632,f2537])).

fof(f2537,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(sK1))
      | r2_hidden(k4_tarski(X5,X4),sK1) ) ),
    inference(resolution,[],[f2493,f182])).

fof(f182,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k4_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X3,X2),k4_relat_1(sK1))
      | r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(superposition,[],[f96,f114])).

fof(f96,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f89,f62])).

fof(f89,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13632,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),sK1) ),
    inference(subsumption_resolution,[],[f13629,f1902])).

fof(f1902,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(sK0))
      | r2_hidden(k4_tarski(X5,X4),sK0) ) ),
    inference(resolution,[],[f1835,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k4_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,X1),sK0) ) ),
    inference(superposition,[],[f96,f113])).

fof(f13629,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),sK1)
    | ~ r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),sK0) ),
    inference(resolution,[],[f1276,f91])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1276,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1273,f329])).

fof(f1273,plain,
    ( ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f291,f96])).

fof(f291,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(sK0)) ),
    inference(resolution,[],[f242,f91])).

fof(f242,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)))
    | ~ r2_hidden(k4_tarski(sK2(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1))),sK3(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1)),k4_relat_1(k3_xboole_0(sK0,sK1)))),k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK0),k4_relat_1(sK1))) ),
    inference(extensionality_resolution,[],[f67,f58])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
