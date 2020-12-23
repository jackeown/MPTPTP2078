%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:44 EST 2020

% Result     : Theorem 47.44s
% Output     : Refutation 47.59s
% Verified   : 
% Statistics : Number of formulae       :  171 (15383 expanded)
%              Number of leaves         :   23 (4224 expanded)
%              Depth                    :   55
%              Number of atoms          :  465 (105391 expanded)
%              Number of equality atoms :   94 (9693 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57273,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57272,f54])).

fof(f54,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f57272,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f57136,f57246])).

fof(f57246,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f57093,f55521])).

fof(f55521,plain,(
    k9_relat_1(sK1,sK0) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f1125,f49694])).

fof(f49694,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f49607,f53])).

fof(f53,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f49607,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k3_xboole_0(X1,X2) = X1 ) ),
    inference(forward_demodulation,[],[f49606,f32608])).

fof(f32608,plain,(
    ! [X243,X242] : k1_relat_1(sK4(sK2(X242),X243)) = X243 ),
    inference(condensation,[],[f32511])).

fof(f32511,plain,(
    ! [X243,X241,X242,X240] :
      ( k1_relat_1(sK4(sK2(X240),X241)) = X241
      | k1_relat_1(sK4(sK2(X242),X243)) = X243 ) ),
    inference(resolution,[],[f28342,f16960])).

fof(f16960,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X1),X0)
      | k1_relat_1(sK4(X0,X2)) = X2 ) ),
    inference(superposition,[],[f16915,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK4(X0,X1)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK4(X0,X1)),X0)
        & k1_relat_1(sK4(X0,X1)) = X1
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1)),X0)
        & k1_relat_1(sK4(X0,X1)) = X1
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f16915,plain,(
    ! [X16] : ~ r2_hidden(sK2(X16),k1_xboole_0) ),
    inference(resolution,[],[f14105,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f14105,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X22,k1_relat_1(k7_relat_1(sK1,X21)))
      | ~ r2_hidden(sK2(X21),X22) ) ),
    inference(superposition,[],[f13532,f121])).

fof(f121,plain,(
    ! [X3] : k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X3)),k4_xboole_0(X3,k1_relat_1(k7_relat_1(sK1,X3)))) = X3 ),
    inference(resolution,[],[f100,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f100,plain,(
    ! [X3] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X3)),X3) ),
    inference(resolution,[],[f52,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f13532,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(k2_xboole_0(X1,X2)),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f13354,f72])).

fof(f13354,plain,(
    ! [X14,X15,X13] : ~ r2_hidden(sK2(k2_xboole_0(k2_xboole_0(X13,X14),X15)),X13) ),
    inference(resolution,[],[f13331,f94])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f13331,plain,(
    ! [X10,X9] : ~ r2_hidden(sK2(k2_xboole_0(X9,X10)),X9) ),
    inference(resolution,[],[f13326,f94])).

fof(f13326,plain,(
    ! [X0] : ~ r2_hidden(sK2(X0),X0) ),
    inference(subsumption_resolution,[],[f13322,f55])).

fof(f13322,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f13277,f72])).

fof(f13277,plain,(
    ! [X48,X49] : ~ r2_hidden(sK2(k2_xboole_0(X48,k4_xboole_0(X49,k1_xboole_0))),X49) ),
    inference(resolution,[],[f12093,f59])).

fof(f59,plain,(
    ! [X0] : r2_hidden(X0,sK2(X0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK2(X0))
          | r2_tarski(X2,sK2(X0))
          | ~ r1_tarski(X2,sK2(X0)) )
      & ! [X3] :
          ( ( ! [X5] :
                ( r2_hidden(X5,sK3(X0,X3))
                | ~ r1_tarski(X5,X3) )
            & r2_hidden(sK3(X0,X3),sK2(X0)) )
          | ~ r2_hidden(X3,sK2(X0)) )
      & ! [X6,X7] :
          ( r2_hidden(X7,sK2(X0))
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,sK2(X0)) )
      & r2_hidden(X0,sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f43,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( ? [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X4)
                      | ~ r1_tarski(X5,X3) )
                  & r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X1) )
          & ! [X6,X7] :
              ( r2_hidden(X7,X1)
              | ~ r1_tarski(X7,X6)
              | ~ r2_hidden(X6,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK2(X0))
            | r2_tarski(X2,sK2(X0))
            | ~ r1_tarski(X2,sK2(X0)) )
        & ! [X3] :
            ( ? [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X4)
                    | ~ r1_tarski(X5,X3) )
                & r2_hidden(X4,sK2(X0)) )
            | ~ r2_hidden(X3,sK2(X0)) )
        & ! [X7,X6] :
            ( r2_hidden(X7,sK2(X0))
            | ~ r1_tarski(X7,X6)
            | ~ r2_hidden(X6,sK2(X0)) )
        & r2_hidden(X0,sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,X4)
              | ~ r1_tarski(X5,X3) )
          & r2_hidden(X4,sK2(X0)) )
     => ( ! [X5] :
            ( r2_hidden(X5,sK3(X0,X3))
            | ~ r1_tarski(X5,X3) )
        & r2_hidden(sK3(X0,X3),sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).

fof(f12093,plain,(
    ! [X24,X23,X22] :
      ( ~ r2_hidden(k2_xboole_0(X24,k4_xboole_0(X23,k1_xboole_0)),X22)
      | ~ r2_hidden(X22,X23) ) ),
    inference(resolution,[],[f10639,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f10639,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,k2_xboole_0(X5,k4_xboole_0(X4,k1_xboole_0)))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f10635,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10635,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f10631,f55])).

fof(f10631,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f10455,f72])).

fof(f10455,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(k1_xboole_0,X2))
      | r2_hidden(X0,X2) ) ),
    inference(condensation,[],[f10437])).

fof(f10437,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k2_xboole_0(k1_xboole_0,X2)) ) ),
    inference(resolution,[],[f10436,f95])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10436,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f10435,f55])).

fof(f10435,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,X1) ) ),
    inference(forward_demodulation,[],[f10434,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK4(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK4(X0,X1)) = X1
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10434,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(k1_relat_1(sK4(X0,k1_xboole_0)),X1) ) ),
    inference(forward_demodulation,[],[f10433,f90])).

fof(f10433,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(sK4(X0,k1_xboole_0)))
      | r2_hidden(X2,X1)
      | ~ r1_tarski(k1_relat_1(sK4(X0,k1_xboole_0)),X1) ) ),
    inference(subsumption_resolution,[],[f10432,f92])).

fof(f92,plain,(
    ! [X0] : v1_relat_1(sK4(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK4(X0,X1))
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10432,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(sK4(X0,k1_xboole_0)))
      | r2_hidden(X2,X1)
      | ~ r1_tarski(k1_relat_1(sK4(X0,k1_xboole_0)),X1)
      | ~ v1_relat_1(sK4(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f9981,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f9981,plain,(
    ! [X94,X95,X93] :
      ( ~ r2_hidden(X93,k1_relat_1(k7_relat_1(sK4(X95,k1_xboole_0),X94)))
      | r2_hidden(X93,X94) ) ),
    inference(resolution,[],[f8198,f92])).

fof(f8198,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X6)
      | r2_hidden(X8,X7)
      | ~ r2_hidden(X8,k1_relat_1(k7_relat_1(X6,X7))) ) ),
    inference(superposition,[],[f8152,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f8152,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
      | r2_hidden(X19,X18) ) ),
    inference(superposition,[],[f94,f5089])).

fof(f5089,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X8,k3_xboole_0(X7,X8))) = X8 ),
    inference(backward_demodulation,[],[f1976,f5079])).

fof(f5079,plain,(
    ! [X10,X9] : k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X9),X10)) = k3_xboole_0(X9,X10) ),
    inference(backward_demodulation,[],[f944,f5067])).

fof(f5067,plain,(
    ! [X24] : k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X24)) = X24 ),
    inference(condensation,[],[f5059])).

fof(f5059,plain,(
    ! [X24,X23] :
      ( k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X23)) = X23
      | k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X24)) = X24 ) ),
    inference(resolution,[],[f640,f635])).

fof(f635,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2(k1_relat_1(sK1)))
      | k1_relat_1(sK4(X0,X1)) = X1 ) ),
    inference(superposition,[],[f626,f77])).

fof(f626,plain,(
    r2_hidden(k1_xboole_0,sK2(k1_relat_1(sK1))) ),
    inference(condensation,[],[f614])).

fof(f614,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
      | r2_hidden(k1_xboole_0,sK2(k1_relat_1(sK1))) ) ),
    inference(resolution,[],[f607,f95])).

fof(f607,plain,(
    ! [X2] : r2_hidden(k1_xboole_0,k2_xboole_0(sK2(k1_relat_1(sK1)),X2)) ),
    inference(resolution,[],[f281,f55])).

fof(f281,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,sK0)
      | r2_hidden(X5,k2_xboole_0(sK2(k1_relat_1(sK1)),X6)) ) ),
    inference(resolution,[],[f241,f94])).

fof(f241,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2(k1_relat_1(sK1)))
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f238,f60])).

fof(f60,plain,(
    ! [X6,X0,X7] :
      ( r2_hidden(X7,sK2(X0))
      | ~ r1_tarski(X7,X6)
      | ~ r2_hidden(X6,sK2(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f238,plain,(
    r2_hidden(sK0,sK2(k1_relat_1(sK1))) ),
    inference(resolution,[],[f106,f59])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_relat_1(sK1),sK2(X1))
      | r2_hidden(sK0,sK2(X1)) ) ),
    inference(resolution,[],[f53,f60])).

fof(f640,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_relat_1(sK1)),X0)
      | k1_relat_1(sK4(X0,X1)) = X1 ) ),
    inference(superposition,[],[f632,f77])).

fof(f632,plain,(
    ~ r2_hidden(sK2(k1_relat_1(sK1)),k1_xboole_0) ),
    inference(resolution,[],[f626,f71])).

fof(f944,plain,(
    ! [X10,X9] : k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X9),X10)) = k3_xboole_0(k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X9)),X10) ),
    inference(resolution,[],[f938,f69])).

fof(f938,plain,(
    ! [X18] : v1_relat_1(sK4(sK2(k1_relat_1(sK1)),X18)) ),
    inference(condensation,[],[f932])).

fof(f932,plain,(
    ! [X17,X18] :
      ( v1_relat_1(sK4(sK2(k1_relat_1(sK1)),X17))
      | v1_relat_1(sK4(sK2(k1_relat_1(sK1)),X18)) ) ),
    inference(resolution,[],[f639,f634])).

fof(f634,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2(k1_relat_1(sK1)))
      | v1_relat_1(sK4(X0,X1)) ) ),
    inference(superposition,[],[f626,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f639,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_relat_1(sK1)),X0)
      | v1_relat_1(sK4(X0,X1)) ) ),
    inference(superposition,[],[f632,f73])).

fof(f1976,plain,(
    ! [X8,X7] : k2_xboole_0(k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X7),X8)),k4_xboole_0(X8,k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X7),X8)))) = X8 ),
    inference(resolution,[],[f943,f72])).

fof(f943,plain,(
    ! [X8,X7] : r1_tarski(k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X7),X8)),X8) ),
    inference(resolution,[],[f938,f68])).

fof(f28342,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK2(X1))
      | k1_relat_1(sK4(X0,X2)) = X2 ) ),
    inference(superposition,[],[f28323,f77])).

fof(f28323,plain,(
    ! [X12] : r2_hidden(k1_xboole_0,sK2(X12)) ),
    inference(superposition,[],[f28259,f5089])).

fof(f28259,plain,(
    ! [X24,X23] : r2_hidden(k1_xboole_0,sK2(k2_xboole_0(X23,X24))) ),
    inference(resolution,[],[f28046,f55])).

fof(f28046,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X8,k1_relat_1(k7_relat_1(sK1,X10)))
      | r2_hidden(X8,sK2(k2_xboole_0(X9,X10))) ) ),
    inference(resolution,[],[f28023,f60])).

fof(f28023,plain,(
    ! [X0,X1] : r2_hidden(k1_relat_1(k7_relat_1(sK1,X0)),sK2(k2_xboole_0(X1,X0))) ),
    inference(resolution,[],[f158,f59])).

fof(f158,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(k2_xboole_0(X9,X7),sK2(X8))
      | r2_hidden(k1_relat_1(k7_relat_1(sK1,X7)),sK2(X8)) ) ),
    inference(resolution,[],[f120,f60])).

fof(f120,plain,(
    ! [X2,X1] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k2_xboole_0(X2,X1)) ),
    inference(resolution,[],[f100,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f49606,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(k1_relat_1(sK4(sK2(X0),X1)),X2) ) ),
    inference(forward_demodulation,[],[f49605,f32608])).

fof(f49605,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k1_relat_1(sK4(sK2(X0),X1))
      | ~ r1_tarski(k1_relat_1(sK4(sK2(X0),X1)),X2) ) ),
    inference(subsumption_resolution,[],[f49540,f11874])).

fof(f11874,plain,(
    ! [X2,X3] : v1_relat_1(sK4(sK2(X2),X3)) ),
    inference(condensation,[],[f11591])).

fof(f11591,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(sK4(sK2(X0),X1))
      | v1_relat_1(sK4(sK2(X2),X3)) ) ),
    inference(resolution,[],[f11223,f10948])).

fof(f10948,plain,(
    ! [X41,X42,X40] :
      ( r2_hidden(X40,X41)
      | v1_relat_1(sK4(sK2(X40),X42)) ) ),
    inference(resolution,[],[f10448,f59])).

fof(f10448,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X0)
      | r2_hidden(X1,X2)
      | v1_relat_1(sK4(X0,X3)) ) ),
    inference(superposition,[],[f10436,f73])).

fof(f11223,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X15,X13)
      | v1_relat_1(sK4(sK2(X13),X14)) ) ),
    inference(resolution,[],[f10948,f71])).

fof(f49540,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k1_relat_1(sK4(sK2(X0),X1))
      | ~ r1_tarski(k1_relat_1(sK4(sK2(X0),X1)),X2)
      | ~ v1_relat_1(sK4(sK2(X0),X1)) ) ),
    inference(superposition,[],[f32620,f70])).

fof(f32620,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X15,X16) = k1_relat_1(k7_relat_1(sK4(sK2(X14),X15),X16)) ),
    inference(backward_demodulation,[],[f11880,f32608])).

fof(f11880,plain,(
    ! [X14,X15,X16] : k1_relat_1(k7_relat_1(sK4(sK2(X14),X15),X16)) = k3_xboole_0(k1_relat_1(sK4(sK2(X14),X15)),X16) ),
    inference(resolution,[],[f11874,f69])).

fof(f1125,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(X0,X1)) = k9_relat_1(sK1,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k7_relat_1(sK1,X0),X1) = k9_relat_1(sK1,X1) ) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f57093,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f110,f55444])).

fof(f55444,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f49694,f190])).

fof(f190,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k1_relat_1(sK1)) ),
    inference(superposition,[],[f101,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f101,plain,(
    ! [X4] : k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(sK1),X4) ),
    inference(resolution,[],[f52,f69])).

fof(f110,plain,(
    ! [X1] : k9_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1))) = k2_relat_1(k7_relat_1(sK1,X1)) ),
    inference(resolution,[],[f99,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f99,plain,(
    ! [X2] : v1_relat_1(k7_relat_1(sK1,X2)) ),
    inference(resolution,[],[f52,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f57136,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f8732,f55444])).

fof(f8732,plain,(
    ! [X88] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X88)),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X88)))) ),
    inference(superposition,[],[f5076,f367])).

fof(f367,plain,(
    ! [X4] : k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4)))) ),
    inference(subsumption_resolution,[],[f364,f99])).

fof(f364,plain,(
    ! [X4] :
      ( k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4))))
      | ~ v1_relat_1(k7_relat_1(sK1,X4)) ) ),
    inference(superposition,[],[f103,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f103,plain,(
    ! [X6,X7] : k10_relat_1(k7_relat_1(sK1,X6),X7) = k3_xboole_0(X6,k10_relat_1(sK1,X7)) ),
    inference(resolution,[],[f52,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f5076,plain,(
    ! [X8,X7] : r1_tarski(k3_xboole_0(X7,X8),X8) ),
    inference(backward_demodulation,[],[f951,f5069])).

fof(f5069,plain,(
    ! [X10,X9] : k1_relat_1(k7_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X9),X10)) = k3_xboole_0(X9,X10) ),
    inference(backward_demodulation,[],[f952,f5056])).

fof(f5056,plain,(
    ! [X16] : k1_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X16)) = X16 ),
    inference(resolution,[],[f640,f59])).

fof(f952,plain,(
    ! [X10,X9] : k1_relat_1(k7_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X9),X10)) = k3_xboole_0(k1_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X9)),X10) ),
    inference(resolution,[],[f931,f69])).

fof(f931,plain,(
    ! [X16] : v1_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X16)) ),
    inference(resolution,[],[f639,f59])).

fof(f951,plain,(
    ! [X8,X7] : r1_tarski(k1_relat_1(k7_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X7),X8)),X8) ),
    inference(resolution,[],[f931,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (17880)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (17872)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (17864)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (17862)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (17857)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (17859)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (17860)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (17884)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (17886)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (17881)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (17867)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (17867)Refutation not found, incomplete strategy% (17867)------------------------------
% 0.21/0.54  % (17867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17867)Memory used [KB]: 10618
% 0.21/0.54  % (17867)Time elapsed: 0.122 s
% 0.21/0.54  % (17867)------------------------------
% 0.21/0.54  % (17867)------------------------------
% 0.21/0.54  % (17877)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (17879)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (17863)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (17873)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (17878)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (17858)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (17883)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (17869)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (17866)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (17865)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (17871)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (17870)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (17876)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (17861)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (17874)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (17882)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (17874)Refutation not found, incomplete strategy% (17874)------------------------------
% 0.21/0.56  % (17874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17874)Memory used [KB]: 10618
% 0.21/0.56  % (17874)Time elapsed: 0.147 s
% 0.21/0.56  % (17874)------------------------------
% 0.21/0.56  % (17874)------------------------------
% 0.21/0.56  % (17885)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (17875)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (17868)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (17879)Refutation not found, incomplete strategy% (17879)------------------------------
% 0.21/0.57  % (17879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (17879)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (17879)Memory used [KB]: 10746
% 0.21/0.57  % (17879)Time elapsed: 0.156 s
% 0.21/0.57  % (17879)------------------------------
% 0.21/0.57  % (17879)------------------------------
% 0.21/0.57  % (17868)Refutation not found, incomplete strategy% (17868)------------------------------
% 0.21/0.57  % (17868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (17868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (17868)Memory used [KB]: 10618
% 0.21/0.57  % (17868)Time elapsed: 0.137 s
% 0.21/0.57  % (17868)------------------------------
% 0.21/0.57  % (17868)------------------------------
% 2.22/0.68  % (17908)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.76/0.74  % (17911)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.76/0.74  % (17910)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.76/0.75  % (17909)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.63/0.85  % (17862)Time limit reached!
% 3.63/0.85  % (17862)------------------------------
% 3.63/0.85  % (17862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.85  % (17862)Termination reason: Time limit
% 3.63/0.85  
% 3.63/0.85  % (17862)Memory used [KB]: 8955
% 3.63/0.85  % (17862)Time elapsed: 0.425 s
% 3.63/0.85  % (17862)------------------------------
% 3.63/0.85  % (17862)------------------------------
% 4.17/0.92  % (17858)Time limit reached!
% 4.17/0.92  % (17858)------------------------------
% 4.17/0.92  % (17858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.92  % (17858)Termination reason: Time limit
% 4.17/0.92  
% 4.17/0.92  % (17858)Memory used [KB]: 7803
% 4.17/0.92  % (17858)Time elapsed: 0.504 s
% 4.17/0.92  % (17858)------------------------------
% 4.17/0.92  % (17858)------------------------------
% 4.17/0.92  % (17869)Time limit reached!
% 4.17/0.92  % (17869)------------------------------
% 4.17/0.92  % (17869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.92  % (17869)Termination reason: Time limit
% 4.17/0.92  % (17869)Termination phase: Saturation
% 4.17/0.92  
% 4.17/0.92  % (17869)Memory used [KB]: 10234
% 4.17/0.92  % (17869)Time elapsed: 0.500 s
% 4.17/0.92  % (17869)------------------------------
% 4.17/0.92  % (17869)------------------------------
% 4.17/0.93  % (17857)Time limit reached!
% 4.17/0.93  % (17857)------------------------------
% 4.17/0.93  % (17857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.93  % (17857)Termination reason: Time limit
% 4.17/0.93  
% 4.17/0.93  % (17857)Memory used [KB]: 4477
% 4.17/0.93  % (17857)Time elapsed: 0.513 s
% 4.17/0.93  % (17857)------------------------------
% 4.17/0.93  % (17857)------------------------------
% 4.46/0.99  % (17912)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.46/1.01  % (17914)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.46/1.02  % (17911)Time limit reached!
% 4.46/1.02  % (17911)------------------------------
% 4.46/1.02  % (17911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/1.02  % (17911)Termination reason: Time limit
% 4.46/1.02  
% 4.46/1.02  % (17911)Memory used [KB]: 6908
% 4.46/1.02  % (17911)Time elapsed: 0.407 s
% 4.46/1.02  % (17911)------------------------------
% 4.46/1.02  % (17911)------------------------------
% 4.46/1.02  % (17913)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.03/1.03  % (17885)Time limit reached!
% 5.03/1.03  % (17885)------------------------------
% 5.03/1.03  % (17885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.03  % (17885)Termination reason: Time limit
% 5.03/1.03  
% 5.03/1.03  % (17885)Memory used [KB]: 9210
% 5.03/1.03  % (17885)Time elapsed: 0.619 s
% 5.03/1.03  % (17885)------------------------------
% 5.03/1.03  % (17885)------------------------------
% 5.03/1.04  % (17873)Time limit reached!
% 5.03/1.04  % (17873)------------------------------
% 5.03/1.04  % (17873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.04  % (17873)Termination reason: Time limit
% 5.03/1.04  
% 5.03/1.04  % (17873)Memory used [KB]: 16886
% 5.03/1.04  % (17873)Time elapsed: 0.627 s
% 5.03/1.04  % (17873)------------------------------
% 5.03/1.04  % (17873)------------------------------
% 5.03/1.07  % (17864)Time limit reached!
% 5.03/1.07  % (17864)------------------------------
% 5.03/1.07  % (17864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.07  % (17864)Termination reason: Time limit
% 5.03/1.07  
% 5.03/1.07  % (17864)Memory used [KB]: 11513
% 5.03/1.07  % (17864)Time elapsed: 0.612 s
% 5.03/1.07  % (17864)------------------------------
% 5.03/1.07  % (17864)------------------------------
% 5.36/1.12  % (17915)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.36/1.13  % (17916)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.23/1.17  % (17917)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.23/1.17  % (17918)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.39/1.20  % (17919)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.39/1.21  % (17878)Time limit reached!
% 6.39/1.21  % (17878)------------------------------
% 6.39/1.21  % (17878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.39/1.21  % (17878)Termination reason: Time limit
% 6.39/1.21  % (17878)Termination phase: Saturation
% 6.39/1.21  
% 6.39/1.21  % (17878)Memory used [KB]: 7931
% 6.39/1.21  % (17878)Time elapsed: 0.800 s
% 6.39/1.21  % (17878)------------------------------
% 6.39/1.21  % (17878)------------------------------
% 6.98/1.29  % (17912)Time limit reached!
% 6.98/1.29  % (17912)------------------------------
% 6.98/1.29  % (17912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.98/1.29  % (17912)Termination reason: Time limit
% 6.98/1.29  % (17912)Termination phase: Saturation
% 6.98/1.29  
% 6.98/1.29  % (17912)Memory used [KB]: 13176
% 6.98/1.29  % (17912)Time elapsed: 0.400 s
% 6.98/1.29  % (17912)------------------------------
% 6.98/1.29  % (17912)------------------------------
% 7.88/1.37  % (17920)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.88/1.42  % (17859)Time limit reached!
% 7.88/1.42  % (17859)------------------------------
% 7.88/1.42  % (17859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.42  % (17859)Termination reason: Time limit
% 7.88/1.42  % (17859)Termination phase: Saturation
% 7.88/1.42  
% 7.88/1.42  % (17859)Memory used [KB]: 18421
% 7.88/1.42  % (17859)Time elapsed: 1.005 s
% 7.88/1.42  % (17859)------------------------------
% 7.88/1.42  % (17859)------------------------------
% 7.88/1.43  % (17921)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.23/1.60  % (17922)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.73/1.67  % (17883)Time limit reached!
% 9.73/1.67  % (17883)------------------------------
% 9.73/1.67  % (17883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.69  % (17883)Termination reason: Time limit
% 10.35/1.69  
% 10.35/1.69  % (17883)Memory used [KB]: 20852
% 10.35/1.69  % (17883)Time elapsed: 1.238 s
% 10.35/1.69  % (17883)------------------------------
% 10.35/1.69  % (17883)------------------------------
% 10.35/1.71  % (17881)Time limit reached!
% 10.35/1.71  % (17881)------------------------------
% 10.35/1.71  % (17881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.73  % (17881)Termination reason: Time limit
% 10.35/1.73  % (17881)Termination phase: Saturation
% 10.35/1.73  
% 10.35/1.73  % (17881)Memory used [KB]: 26225
% 10.35/1.73  % (17881)Time elapsed: 1.300 s
% 10.35/1.73  % (17881)------------------------------
% 10.35/1.73  % (17881)------------------------------
% 10.99/1.77  % (17920)Time limit reached!
% 10.99/1.77  % (17920)------------------------------
% 10.99/1.77  % (17920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.99/1.78  % (17920)Termination reason: Time limit
% 10.99/1.78  
% 10.99/1.78  % (17920)Memory used [KB]: 3326
% 10.99/1.78  % (17920)Time elapsed: 0.513 s
% 10.99/1.78  % (17920)------------------------------
% 10.99/1.78  % (17920)------------------------------
% 10.99/1.78  % (17872)Time limit reached!
% 10.99/1.78  % (17872)------------------------------
% 10.99/1.78  % (17872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.22/1.80  % (17872)Termination reason: Time limit
% 11.22/1.80  
% 11.22/1.80  % (17872)Memory used [KB]: 19189
% 11.22/1.80  % (17872)Time elapsed: 1.322 s
% 11.22/1.80  % (17872)------------------------------
% 11.22/1.80  % (17872)------------------------------
% 11.22/1.82  % (17923)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.59/1.88  % (17924)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.05/1.92  % (17925)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.05/1.93  % (17884)Time limit reached!
% 12.05/1.93  % (17884)------------------------------
% 12.05/1.93  % (17884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.05/1.93  % (17884)Termination reason: Time limit
% 12.05/1.93  
% 12.05/1.93  % (17884)Memory used [KB]: 14456
% 12.05/1.93  % (17884)Time elapsed: 1.519 s
% 12.05/1.93  % (17884)------------------------------
% 12.05/1.93  % (17884)------------------------------
% 12.05/1.96  % (17861)Time limit reached!
% 12.05/1.96  % (17861)------------------------------
% 12.05/1.96  % (17861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.05/1.96  % (17926)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.46/1.97  % (17861)Termination reason: Time limit
% 12.46/1.97  % (17861)Termination phase: Saturation
% 12.46/1.97  
% 12.46/1.97  % (17861)Memory used [KB]: 25202
% 12.46/1.97  % (17861)Time elapsed: 1.517 s
% 12.46/1.97  % (17861)------------------------------
% 12.46/1.97  % (17861)------------------------------
% 13.02/2.07  % (17927)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.18/2.10  % (17928)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.51/2.15  % (17924)Time limit reached!
% 13.51/2.15  % (17924)------------------------------
% 13.51/2.15  % (17924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.51/2.15  % (17924)Termination reason: Time limit
% 13.51/2.15  % (17924)Termination phase: Saturation
% 13.51/2.15  
% 13.51/2.15  % (17924)Memory used [KB]: 4349
% 13.51/2.15  % (17924)Time elapsed: 0.400 s
% 13.51/2.15  % (17924)------------------------------
% 13.51/2.15  % (17924)------------------------------
% 13.51/2.21  % (17914)Time limit reached!
% 13.51/2.21  % (17914)------------------------------
% 13.51/2.21  % (17914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.51/2.21  % (17914)Termination reason: Time limit
% 13.51/2.21  
% 13.51/2.21  % (17914)Memory used [KB]: 16630
% 13.51/2.21  % (17914)Time elapsed: 1.223 s
% 13.51/2.21  % (17914)------------------------------
% 13.51/2.21  % (17914)------------------------------
% 14.67/2.27  % (17871)Time limit reached!
% 14.67/2.27  % (17871)------------------------------
% 14.67/2.27  % (17871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.67/2.27  % (17871)Termination reason: Time limit
% 14.67/2.27  
% 14.67/2.27  % (17871)Memory used [KB]: 9850
% 14.67/2.27  % (17871)Time elapsed: 1.846 s
% 14.67/2.27  % (17871)------------------------------
% 14.67/2.27  % (17871)------------------------------
% 15.11/2.31  % (17910)Time limit reached!
% 15.11/2.31  % (17910)------------------------------
% 15.11/2.31  % (17910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.11/2.31  % (17910)Termination reason: Time limit
% 15.11/2.31  % (17910)Termination phase: Saturation
% 15.11/2.31  
% 15.11/2.31  % (17910)Memory used [KB]: 15095
% 15.11/2.31  % (17910)Time elapsed: 1.703 s
% 15.11/2.31  % (17910)------------------------------
% 15.11/2.31  % (17910)------------------------------
% 15.11/2.32  % (17929)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.11/2.32  % (17930)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.78/2.37  % (17927)Time limit reached!
% 15.78/2.37  % (17927)------------------------------
% 15.78/2.37  % (17927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.78/2.37  % (17927)Termination reason: Time limit
% 15.78/2.37  
% 15.78/2.37  % (17927)Memory used [KB]: 3582
% 15.78/2.37  % (17927)Time elapsed: 0.420 s
% 15.78/2.37  % (17927)------------------------------
% 15.78/2.37  % (17927)------------------------------
% 15.96/2.39  % (17931)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.23/2.45  % (17863)Time limit reached!
% 16.23/2.45  % (17863)------------------------------
% 16.23/2.45  % (17863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.23/2.45  % (17863)Termination reason: Time limit
% 16.23/2.45  
% 16.23/2.45  % (17863)Memory used [KB]: 22259
% 16.23/2.45  % (17863)Time elapsed: 2.011 s
% 16.23/2.45  % (17863)------------------------------
% 16.23/2.45  % (17863)------------------------------
% 16.23/2.47  % (17875)Time limit reached!
% 16.23/2.47  % (17875)------------------------------
% 16.23/2.47  % (17875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.23/2.47  % (17875)Termination reason: Time limit
% 16.23/2.47  
% 16.23/2.47  % (17875)Memory used [KB]: 15863
% 16.23/2.47  % (17875)Time elapsed: 2.017 s
% 16.23/2.47  % (17875)------------------------------
% 16.23/2.47  % (17875)------------------------------
% 16.23/2.50  % (17932)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.80/2.55  % (17933)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.19/2.60  % (17935)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 17.19/2.61  % (17934)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.81/2.77  % (17932)Time limit reached!
% 18.81/2.77  % (17932)------------------------------
% 18.81/2.77  % (17932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.81/2.77  % (17916)Time limit reached!
% 18.81/2.77  % (17916)------------------------------
% 18.81/2.77  % (17916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.81/2.77  % (17932)Termination reason: Time limit
% 18.81/2.77  % (17932)Termination phase: Saturation
% 18.81/2.77  
% 18.81/2.77  % (17932)Memory used [KB]: 11385
% 18.81/2.77  % (17932)Time elapsed: 0.422 s
% 18.81/2.77  % (17932)------------------------------
% 18.81/2.77  % (17932)------------------------------
% 18.81/2.77  % (17916)Termination reason: Time limit
% 18.81/2.77  % (17916)Termination phase: Saturation
% 18.81/2.77  
% 18.81/2.77  % (17916)Memory used [KB]: 20212
% 18.81/2.77  % (17916)Time elapsed: 1.700 s
% 18.81/2.77  % (17916)------------------------------
% 18.81/2.77  % (17916)------------------------------
% 19.48/2.88  % (17934)Time limit reached!
% 19.48/2.88  % (17934)------------------------------
% 19.48/2.88  % (17934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.48/2.88  % (17934)Termination reason: Time limit
% 19.48/2.88  
% 19.48/2.88  % (17934)Memory used [KB]: 8699
% 19.48/2.88  % (17934)Time elapsed: 0.402 s
% 19.48/2.88  % (17934)------------------------------
% 19.48/2.88  % (17934)------------------------------
% 20.03/2.92  % (17923)Time limit reached!
% 20.03/2.92  % (17923)------------------------------
% 20.03/2.92  % (17923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.03/2.92  % (17923)Termination reason: Time limit
% 20.03/2.92  % (17923)Termination phase: Saturation
% 20.03/2.92  
% 20.03/2.92  % (17923)Memory used [KB]: 17782
% 20.03/2.92  % (17923)Time elapsed: 1.200 s
% 20.03/2.92  % (17923)------------------------------
% 20.03/2.92  % (17923)------------------------------
% 21.01/3.03  % (17876)Time limit reached!
% 21.01/3.03  % (17876)------------------------------
% 21.01/3.03  % (17876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.01/3.03  % (17876)Termination reason: Time limit
% 21.01/3.03  % (17876)Termination phase: Saturation
% 21.01/3.03  
% 21.01/3.03  % (17876)Memory used [KB]: 28272
% 21.01/3.03  % (17876)Time elapsed: 2.619 s
% 21.01/3.03  % (17876)------------------------------
% 21.01/3.03  % (17876)------------------------------
% 21.92/3.16  % (17926)Time limit reached!
% 21.92/3.16  % (17926)------------------------------
% 21.92/3.16  % (17926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.92/3.16  % (17926)Termination reason: Time limit
% 21.92/3.16  % (17926)Termination phase: Saturation
% 21.92/3.16  
% 21.92/3.16  % (17926)Memory used [KB]: 21236
% 21.92/3.16  % (17926)Time elapsed: 1.300 s
% 21.92/3.16  % (17926)------------------------------
% 21.92/3.16  % (17926)------------------------------
% 23.66/3.42  % (17870)Time limit reached!
% 23.66/3.42  % (17870)------------------------------
% 23.66/3.42  % (17870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.66/3.42  % (17870)Termination reason: Time limit
% 23.66/3.42  % (17870)Termination phase: Saturation
% 23.66/3.42  
% 23.66/3.42  % (17870)Memory used [KB]: 18549
% 23.66/3.42  % (17870)Time elapsed: 3.007 s
% 23.66/3.42  % (17870)------------------------------
% 23.66/3.42  % (17870)------------------------------
% 24.42/3.44  % (17909)Time limit reached!
% 24.42/3.44  % (17909)------------------------------
% 24.42/3.44  % (17909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.42/3.44  % (17909)Termination reason: Time limit
% 24.42/3.44  
% 24.42/3.44  % (17909)Memory used [KB]: 19061
% 24.42/3.44  % (17909)Time elapsed: 2.814 s
% 24.42/3.44  % (17909)------------------------------
% 24.42/3.44  % (17909)------------------------------
% 29.19/4.05  % (17865)Time limit reached!
% 29.19/4.05  % (17865)------------------------------
% 29.19/4.05  % (17865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.19/4.05  % (17865)Termination reason: Time limit
% 29.19/4.05  % (17865)Termination phase: Saturation
% 29.19/4.05  
% 29.19/4.05  % (17865)Memory used [KB]: 28016
% 29.19/4.05  % (17865)Time elapsed: 3.637 s
% 29.19/4.05  % (17865)------------------------------
% 29.19/4.05  % (17865)------------------------------
% 30.95/4.33  % (17886)Time limit reached!
% 30.95/4.33  % (17886)------------------------------
% 30.95/4.33  % (17886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.95/4.33  % (17886)Termination reason: Time limit
% 30.95/4.33  % (17886)Termination phase: Saturation
% 30.95/4.33  
% 30.95/4.33  % (17886)Memory used [KB]: 27376
% 30.95/4.33  % (17886)Time elapsed: 3.900 s
% 30.95/4.33  % (17886)------------------------------
% 30.95/4.33  % (17886)------------------------------
% 36.77/4.98  % (17922)Time limit reached!
% 36.77/4.98  % (17922)------------------------------
% 36.77/4.98  % (17922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.77/4.98  % (17922)Termination reason: Time limit
% 36.77/4.98  % (17922)Termination phase: Saturation
% 36.77/4.98  
% 36.77/4.98  % (17922)Memory used [KB]: 51427
% 36.77/4.98  % (17922)Time elapsed: 3.500 s
% 36.77/4.98  % (17922)------------------------------
% 36.77/4.98  % (17922)------------------------------
% 36.77/5.03  % (17866)Time limit reached!
% 36.77/5.03  % (17866)------------------------------
% 36.77/5.03  % (17866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.77/5.05  % (17866)Termination reason: Time limit
% 36.77/5.05  % (17866)Termination phase: Saturation
% 36.77/5.05  
% 36.77/5.05  % (17866)Memory used [KB]: 57312
% 36.77/5.05  % (17866)Time elapsed: 4.600 s
% 36.77/5.05  % (17866)------------------------------
% 36.77/5.05  % (17866)------------------------------
% 41.56/5.63  % (17860)Time limit reached!
% 41.56/5.63  % (17860)------------------------------
% 41.56/5.63  % (17860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.56/5.65  % (17860)Termination reason: Time limit
% 41.56/5.65  
% 41.56/5.65  % (17860)Memory used [KB]: 50404
% 41.56/5.65  % (17860)Time elapsed: 5.222 s
% 41.56/5.65  % (17860)------------------------------
% 41.56/5.65  % (17860)------------------------------
% 47.44/6.33  % (17880)Refutation found. Thanks to Tanya!
% 47.44/6.33  % SZS status Theorem for theBenchmark
% 47.44/6.33  % SZS output start Proof for theBenchmark
% 47.44/6.33  fof(f57273,plain,(
% 47.44/6.33    $false),
% 47.44/6.33    inference(subsumption_resolution,[],[f57272,f54])).
% 47.44/6.33  fof(f54,plain,(
% 47.44/6.33    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 47.44/6.33    inference(cnf_transformation,[],[f41])).
% 47.44/6.33  fof(f41,plain,(
% 47.44/6.33    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 47.44/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f40])).
% 47.44/6.33  fof(f40,plain,(
% 47.44/6.33    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 47.44/6.33    introduced(choice_axiom,[])).
% 47.44/6.33  fof(f23,plain,(
% 47.44/6.33    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 47.44/6.33    inference(flattening,[],[f22])).
% 47.44/6.33  fof(f22,plain,(
% 47.44/6.33    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 47.44/6.33    inference(ennf_transformation,[],[f20])).
% 47.44/6.33  fof(f20,negated_conjecture,(
% 47.44/6.33    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 47.44/6.33    inference(negated_conjecture,[],[f19])).
% 47.44/6.33  fof(f19,conjecture,(
% 47.44/6.33    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 47.44/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 47.59/6.33  fof(f57272,plain,(
% 47.59/6.33    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 47.59/6.33    inference(forward_demodulation,[],[f57136,f57246])).
% 47.59/6.33  fof(f57246,plain,(
% 47.59/6.33    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 47.59/6.33    inference(forward_demodulation,[],[f57093,f55521])).
% 47.59/6.33  fof(f55521,plain,(
% 47.59/6.33    k9_relat_1(sK1,sK0) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 47.59/6.33    inference(superposition,[],[f1125,f49694])).
% 47.59/6.33  fof(f49694,plain,(
% 47.59/6.33    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 47.59/6.33    inference(resolution,[],[f49607,f53])).
% 47.59/6.33  fof(f53,plain,(
% 47.59/6.33    r1_tarski(sK0,k1_relat_1(sK1))),
% 47.59/6.33    inference(cnf_transformation,[],[f41])).
% 47.59/6.33  fof(f49607,plain,(
% 47.59/6.33    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k3_xboole_0(X1,X2) = X1) )),
% 47.59/6.33    inference(forward_demodulation,[],[f49606,f32608])).
% 47.59/6.33  fof(f32608,plain,(
% 47.59/6.33    ( ! [X243,X242] : (k1_relat_1(sK4(sK2(X242),X243)) = X243) )),
% 47.59/6.33    inference(condensation,[],[f32511])).
% 47.59/6.33  fof(f32511,plain,(
% 47.59/6.33    ( ! [X243,X241,X242,X240] : (k1_relat_1(sK4(sK2(X240),X241)) = X241 | k1_relat_1(sK4(sK2(X242),X243)) = X243) )),
% 47.59/6.33    inference(resolution,[],[f28342,f16960])).
% 47.59/6.33  fof(f16960,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X1),X0) | k1_relat_1(sK4(X0,X2)) = X2) )),
% 47.59/6.33    inference(superposition,[],[f16915,f77])).
% 47.59/6.33  fof(f77,plain,(
% 47.59/6.33    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X1 | k1_xboole_0 = X0) )),
% 47.59/6.33    inference(cnf_transformation,[],[f46])).
% 47.59/6.33  fof(f46,plain,(
% 47.59/6.33    ! [X0,X1] : ((r1_tarski(k2_relat_1(sK4(X0,X1)),X0) & k1_relat_1(sK4(X0,X1)) = X1 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 47.59/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f45])).
% 47.59/6.33  fof(f45,plain,(
% 47.59/6.33    ! [X1,X0] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(k2_relat_1(sK4(X0,X1)),X0) & k1_relat_1(sK4(X0,X1)) = X1 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 47.59/6.33    introduced(choice_axiom,[])).
% 47.59/6.33  fof(f37,plain,(
% 47.59/6.33    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 47.59/6.33    inference(flattening,[],[f36])).
% 47.59/6.33  fof(f36,plain,(
% 47.59/6.33    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & (v1_funct_1(X2) & v1_relat_1(X2))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 47.59/6.33    inference(ennf_transformation,[],[f18])).
% 47.59/6.33  fof(f18,axiom,(
% 47.59/6.33    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 47.59/6.33  fof(f16915,plain,(
% 47.59/6.33    ( ! [X16] : (~r2_hidden(sK2(X16),k1_xboole_0)) )),
% 47.59/6.33    inference(resolution,[],[f14105,f55])).
% 47.59/6.33  fof(f55,plain,(
% 47.59/6.33    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f6])).
% 47.59/6.33  fof(f6,axiom,(
% 47.59/6.33    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 47.59/6.33  fof(f14105,plain,(
% 47.59/6.33    ( ! [X21,X22] : (~r1_tarski(X22,k1_relat_1(k7_relat_1(sK1,X21))) | ~r2_hidden(sK2(X21),X22)) )),
% 47.59/6.33    inference(superposition,[],[f13532,f121])).
% 47.59/6.33  fof(f121,plain,(
% 47.59/6.33    ( ! [X3] : (k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X3)),k4_xboole_0(X3,k1_relat_1(k7_relat_1(sK1,X3)))) = X3) )),
% 47.59/6.33    inference(resolution,[],[f100,f72])).
% 47.59/6.33  fof(f72,plain,(
% 47.59/6.33    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f35])).
% 47.59/6.33  fof(f35,plain,(
% 47.59/6.33    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 47.59/6.33    inference(ennf_transformation,[],[f7])).
% 47.59/6.33  fof(f7,axiom,(
% 47.59/6.33    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 47.59/6.33  fof(f100,plain,(
% 47.59/6.33    ( ! [X3] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X3)),X3)) )),
% 47.59/6.33    inference(resolution,[],[f52,f68])).
% 47.59/6.33  fof(f68,plain,(
% 47.59/6.33    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f30])).
% 47.59/6.33  fof(f30,plain,(
% 47.59/6.33    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 47.59/6.33    inference(ennf_transformation,[],[f14])).
% 47.59/6.33  fof(f14,axiom,(
% 47.59/6.33    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 47.59/6.33  fof(f52,plain,(
% 47.59/6.33    v1_relat_1(sK1)),
% 47.59/6.33    inference(cnf_transformation,[],[f41])).
% 47.59/6.33  fof(f13532,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (~r2_hidden(sK2(k2_xboole_0(X1,X2)),X0) | ~r1_tarski(X0,X1)) )),
% 47.59/6.33    inference(superposition,[],[f13354,f72])).
% 47.59/6.33  fof(f13354,plain,(
% 47.59/6.33    ( ! [X14,X15,X13] : (~r2_hidden(sK2(k2_xboole_0(k2_xboole_0(X13,X14),X15)),X13)) )),
% 47.59/6.33    inference(resolution,[],[f13331,f94])).
% 47.59/6.33  fof(f94,plain,(
% 47.59/6.33    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 47.59/6.33    inference(equality_resolution,[],[f84])).
% 47.59/6.33  fof(f84,plain,(
% 47.59/6.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 47.59/6.33    inference(cnf_transformation,[],[f51])).
% 47.59/6.33  fof(f51,plain,(
% 47.59/6.33    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.59/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 47.59/6.33  fof(f50,plain,(
% 47.59/6.33    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 47.59/6.33    introduced(choice_axiom,[])).
% 47.59/6.33  fof(f49,plain,(
% 47.59/6.33    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.59/6.33    inference(rectify,[],[f48])).
% 47.59/6.33  fof(f48,plain,(
% 47.59/6.33    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.59/6.33    inference(flattening,[],[f47])).
% 47.59/6.33  fof(f47,plain,(
% 47.59/6.33    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.59/6.33    inference(nnf_transformation,[],[f3])).
% 47.59/6.33  fof(f3,axiom,(
% 47.59/6.33    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 47.59/6.33  fof(f13331,plain,(
% 47.59/6.33    ( ! [X10,X9] : (~r2_hidden(sK2(k2_xboole_0(X9,X10)),X9)) )),
% 47.59/6.33    inference(resolution,[],[f13326,f94])).
% 47.59/6.33  fof(f13326,plain,(
% 47.59/6.33    ( ! [X0] : (~r2_hidden(sK2(X0),X0)) )),
% 47.59/6.33    inference(subsumption_resolution,[],[f13322,f55])).
% 47.59/6.33  fof(f13322,plain,(
% 47.59/6.33    ( ! [X0] : (~r2_hidden(sK2(X0),X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 47.59/6.33    inference(superposition,[],[f13277,f72])).
% 47.59/6.33  fof(f13277,plain,(
% 47.59/6.33    ( ! [X48,X49] : (~r2_hidden(sK2(k2_xboole_0(X48,k4_xboole_0(X49,k1_xboole_0))),X49)) )),
% 47.59/6.33    inference(resolution,[],[f12093,f59])).
% 47.59/6.33  fof(f59,plain,(
% 47.59/6.33    ( ! [X0] : (r2_hidden(X0,sK2(X0))) )),
% 47.59/6.33    inference(cnf_transformation,[],[f44])).
% 47.59/6.33  fof(f44,plain,(
% 47.59/6.33    ! [X0] : (! [X2] : (r2_hidden(X2,sK2(X0)) | r2_tarski(X2,sK2(X0)) | ~r1_tarski(X2,sK2(X0))) & ! [X3] : ((! [X5] : (r2_hidden(X5,sK3(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK3(X0,X3),sK2(X0))) | ~r2_hidden(X3,sK2(X0))) & ! [X6,X7] : (r2_hidden(X7,sK2(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK2(X0))) & r2_hidden(X0,sK2(X0)))),
% 47.59/6.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f43,f42])).
% 47.59/6.33  fof(f42,plain,(
% 47.59/6.33    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(X2,sK2(X0)) | r2_tarski(X2,sK2(X0)) | ~r1_tarski(X2,sK2(X0))) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK2(X0))) | ~r2_hidden(X3,sK2(X0))) & ! [X7,X6] : (r2_hidden(X7,sK2(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK2(X0))) & r2_hidden(X0,sK2(X0))))),
% 47.59/6.33    introduced(choice_axiom,[])).
% 47.59/6.33  fof(f43,plain,(
% 47.59/6.33    ! [X3,X0] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK2(X0))) => (! [X5] : (r2_hidden(X5,sK3(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK3(X0,X3),sK2(X0))))),
% 47.59/6.33    introduced(choice_axiom,[])).
% 47.59/6.33  fof(f28,plain,(
% 47.59/6.33    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1))),
% 47.59/6.33    inference(flattening,[],[f27])).
% 47.59/6.33  fof(f27,plain,(
% 47.59/6.33    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | (~r1_tarski(X7,X6) | ~r2_hidden(X6,X1))) & r2_hidden(X0,X1))),
% 47.59/6.33    inference(ennf_transformation,[],[f21])).
% 47.59/6.33  fof(f21,plain,(
% 47.59/6.33    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 47.59/6.33    inference(rectify,[],[f9])).
% 47.59/6.33  fof(f9,axiom,(
% 47.59/6.33    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : ~(! [X3] : ~(! [X4] : (r1_tarski(X4,X2) => r2_hidden(X4,X3)) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).
% 47.59/6.33  fof(f12093,plain,(
% 47.59/6.33    ( ! [X24,X23,X22] : (~r2_hidden(k2_xboole_0(X24,k4_xboole_0(X23,k1_xboole_0)),X22) | ~r2_hidden(X22,X23)) )),
% 47.59/6.33    inference(resolution,[],[f10639,f71])).
% 47.59/6.33  fof(f71,plain,(
% 47.59/6.33    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f34])).
% 47.59/6.33  fof(f34,plain,(
% 47.59/6.33    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 47.59/6.33    inference(ennf_transformation,[],[f1])).
% 47.59/6.33  fof(f1,axiom,(
% 47.59/6.33    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 47.59/6.33  fof(f10639,plain,(
% 47.59/6.33    ( ! [X4,X5,X3] : (r2_hidden(X3,k2_xboole_0(X5,k4_xboole_0(X4,k1_xboole_0))) | ~r2_hidden(X3,X4)) )),
% 47.59/6.33    inference(resolution,[],[f10635,f93])).
% 47.59/6.33  fof(f93,plain,(
% 47.59/6.33    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 47.59/6.33    inference(equality_resolution,[],[f85])).
% 47.59/6.33  fof(f85,plain,(
% 47.59/6.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 47.59/6.33    inference(cnf_transformation,[],[f51])).
% 47.59/6.33  fof(f10635,plain,(
% 47.59/6.33    ( ! [X0,X1] : (r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 47.59/6.33    inference(subsumption_resolution,[],[f10631,f55])).
% 47.59/6.33  fof(f10631,plain,(
% 47.59/6.33    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,X0)) )),
% 47.59/6.33    inference(superposition,[],[f10455,f72])).
% 47.59/6.33  fof(f10455,plain,(
% 47.59/6.33    ( ! [X2,X0] : (~r2_hidden(X0,k2_xboole_0(k1_xboole_0,X2)) | r2_hidden(X0,X2)) )),
% 47.59/6.33    inference(condensation,[],[f10437])).
% 47.59/6.33  fof(f10437,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~r2_hidden(X0,k2_xboole_0(k1_xboole_0,X2))) )),
% 47.59/6.33    inference(resolution,[],[f10436,f95])).
% 47.59/6.33  fof(f95,plain,(
% 47.59/6.33    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 47.59/6.33    inference(equality_resolution,[],[f83])).
% 47.59/6.33  fof(f83,plain,(
% 47.59/6.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 47.59/6.33    inference(cnf_transformation,[],[f51])).
% 47.59/6.33  fof(f10436,plain,(
% 47.59/6.33    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,X1)) )),
% 47.59/6.33    inference(subsumption_resolution,[],[f10435,f55])).
% 47.59/6.33  fof(f10435,plain,(
% 47.59/6.33    ( ! [X2,X1] : (~r1_tarski(k1_xboole_0,X1) | ~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,X1)) )),
% 47.59/6.33    inference(forward_demodulation,[],[f10434,f90])).
% 47.59/6.33  fof(f90,plain,(
% 47.59/6.33    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK4(X0,k1_xboole_0))) )),
% 47.59/6.33    inference(equality_resolution,[],[f78])).
% 47.59/6.33  fof(f78,plain,(
% 47.59/6.33    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X1 | k1_xboole_0 != X1) )),
% 47.59/6.33    inference(cnf_transformation,[],[f46])).
% 47.59/6.33  fof(f10434,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,X1) | ~r1_tarski(k1_relat_1(sK4(X0,k1_xboole_0)),X1)) )),
% 47.59/6.33    inference(forward_demodulation,[],[f10433,f90])).
% 47.59/6.33  fof(f10433,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(sK4(X0,k1_xboole_0))) | r2_hidden(X2,X1) | ~r1_tarski(k1_relat_1(sK4(X0,k1_xboole_0)),X1)) )),
% 47.59/6.33    inference(subsumption_resolution,[],[f10432,f92])).
% 47.59/6.33  fof(f92,plain,(
% 47.59/6.33    ( ! [X0] : (v1_relat_1(sK4(X0,k1_xboole_0))) )),
% 47.59/6.33    inference(equality_resolution,[],[f74])).
% 47.59/6.33  fof(f74,plain,(
% 47.59/6.33    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1)) | k1_xboole_0 != X1) )),
% 47.59/6.33    inference(cnf_transformation,[],[f46])).
% 47.59/6.33  fof(f10432,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(sK4(X0,k1_xboole_0))) | r2_hidden(X2,X1) | ~r1_tarski(k1_relat_1(sK4(X0,k1_xboole_0)),X1) | ~v1_relat_1(sK4(X0,k1_xboole_0))) )),
% 47.59/6.33    inference(superposition,[],[f9981,f70])).
% 47.59/6.33  fof(f70,plain,(
% 47.59/6.33    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f33])).
% 47.59/6.33  fof(f33,plain,(
% 47.59/6.33    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 47.59/6.33    inference(flattening,[],[f32])).
% 47.59/6.33  fof(f32,plain,(
% 47.59/6.33    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 47.59/6.33    inference(ennf_transformation,[],[f16])).
% 47.59/6.33  fof(f16,axiom,(
% 47.59/6.33    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 47.59/6.33  fof(f9981,plain,(
% 47.59/6.33    ( ! [X94,X95,X93] : (~r2_hidden(X93,k1_relat_1(k7_relat_1(sK4(X95,k1_xboole_0),X94))) | r2_hidden(X93,X94)) )),
% 47.59/6.33    inference(resolution,[],[f8198,f92])).
% 47.59/6.33  fof(f8198,plain,(
% 47.59/6.33    ( ! [X6,X8,X7] : (~v1_relat_1(X6) | r2_hidden(X8,X7) | ~r2_hidden(X8,k1_relat_1(k7_relat_1(X6,X7)))) )),
% 47.59/6.33    inference(superposition,[],[f8152,f69])).
% 47.59/6.33  fof(f69,plain,(
% 47.59/6.33    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f31])).
% 47.59/6.33  fof(f31,plain,(
% 47.59/6.33    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 47.59/6.33    inference(ennf_transformation,[],[f15])).
% 47.59/6.33  fof(f15,axiom,(
% 47.59/6.33    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 47.59/6.33  fof(f8152,plain,(
% 47.59/6.33    ( ! [X19,X17,X18] : (~r2_hidden(X19,k3_xboole_0(X17,X18)) | r2_hidden(X19,X18)) )),
% 47.59/6.33    inference(superposition,[],[f94,f5089])).
% 47.59/6.33  fof(f5089,plain,(
% 47.59/6.33    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X8,k3_xboole_0(X7,X8))) = X8) )),
% 47.59/6.33    inference(backward_demodulation,[],[f1976,f5079])).
% 47.59/6.33  fof(f5079,plain,(
% 47.59/6.33    ( ! [X10,X9] : (k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X9),X10)) = k3_xboole_0(X9,X10)) )),
% 47.59/6.33    inference(backward_demodulation,[],[f944,f5067])).
% 47.59/6.33  fof(f5067,plain,(
% 47.59/6.33    ( ! [X24] : (k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X24)) = X24) )),
% 47.59/6.33    inference(condensation,[],[f5059])).
% 47.59/6.33  fof(f5059,plain,(
% 47.59/6.33    ( ! [X24,X23] : (k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X23)) = X23 | k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X24)) = X24) )),
% 47.59/6.33    inference(resolution,[],[f640,f635])).
% 47.59/6.33  fof(f635,plain,(
% 47.59/6.33    ( ! [X0,X1] : (r2_hidden(X0,sK2(k1_relat_1(sK1))) | k1_relat_1(sK4(X0,X1)) = X1) )),
% 47.59/6.33    inference(superposition,[],[f626,f77])).
% 47.59/6.33  fof(f626,plain,(
% 47.59/6.33    r2_hidden(k1_xboole_0,sK2(k1_relat_1(sK1)))),
% 47.59/6.33    inference(condensation,[],[f614])).
% 47.59/6.33  fof(f614,plain,(
% 47.59/6.33    ( ! [X0] : (r2_hidden(k1_xboole_0,X0) | r2_hidden(k1_xboole_0,sK2(k1_relat_1(sK1)))) )),
% 47.59/6.33    inference(resolution,[],[f607,f95])).
% 47.59/6.33  fof(f607,plain,(
% 47.59/6.33    ( ! [X2] : (r2_hidden(k1_xboole_0,k2_xboole_0(sK2(k1_relat_1(sK1)),X2))) )),
% 47.59/6.33    inference(resolution,[],[f281,f55])).
% 47.59/6.33  fof(f281,plain,(
% 47.59/6.33    ( ! [X6,X5] : (~r1_tarski(X5,sK0) | r2_hidden(X5,k2_xboole_0(sK2(k1_relat_1(sK1)),X6))) )),
% 47.59/6.33    inference(resolution,[],[f241,f94])).
% 47.59/6.33  fof(f241,plain,(
% 47.59/6.33    ( ! [X0] : (r2_hidden(X0,sK2(k1_relat_1(sK1))) | ~r1_tarski(X0,sK0)) )),
% 47.59/6.33    inference(resolution,[],[f238,f60])).
% 47.59/6.33  fof(f60,plain,(
% 47.59/6.33    ( ! [X6,X0,X7] : (r2_hidden(X7,sK2(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK2(X0))) )),
% 47.59/6.33    inference(cnf_transformation,[],[f44])).
% 47.59/6.33  fof(f238,plain,(
% 47.59/6.33    r2_hidden(sK0,sK2(k1_relat_1(sK1)))),
% 47.59/6.33    inference(resolution,[],[f106,f59])).
% 47.59/6.33  fof(f106,plain,(
% 47.59/6.33    ( ! [X1] : (~r2_hidden(k1_relat_1(sK1),sK2(X1)) | r2_hidden(sK0,sK2(X1))) )),
% 47.59/6.33    inference(resolution,[],[f53,f60])).
% 47.59/6.33  fof(f640,plain,(
% 47.59/6.33    ( ! [X0,X1] : (~r2_hidden(sK2(k1_relat_1(sK1)),X0) | k1_relat_1(sK4(X0,X1)) = X1) )),
% 47.59/6.33    inference(superposition,[],[f632,f77])).
% 47.59/6.33  fof(f632,plain,(
% 47.59/6.33    ~r2_hidden(sK2(k1_relat_1(sK1)),k1_xboole_0)),
% 47.59/6.33    inference(resolution,[],[f626,f71])).
% 47.59/6.33  fof(f944,plain,(
% 47.59/6.33    ( ! [X10,X9] : (k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X9),X10)) = k3_xboole_0(k1_relat_1(sK4(sK2(k1_relat_1(sK1)),X9)),X10)) )),
% 47.59/6.33    inference(resolution,[],[f938,f69])).
% 47.59/6.33  fof(f938,plain,(
% 47.59/6.33    ( ! [X18] : (v1_relat_1(sK4(sK2(k1_relat_1(sK1)),X18))) )),
% 47.59/6.33    inference(condensation,[],[f932])).
% 47.59/6.33  fof(f932,plain,(
% 47.59/6.33    ( ! [X17,X18] : (v1_relat_1(sK4(sK2(k1_relat_1(sK1)),X17)) | v1_relat_1(sK4(sK2(k1_relat_1(sK1)),X18))) )),
% 47.59/6.33    inference(resolution,[],[f639,f634])).
% 47.59/6.33  fof(f634,plain,(
% 47.59/6.33    ( ! [X0,X1] : (r2_hidden(X0,sK2(k1_relat_1(sK1))) | v1_relat_1(sK4(X0,X1))) )),
% 47.59/6.33    inference(superposition,[],[f626,f73])).
% 47.59/6.33  fof(f73,plain,(
% 47.59/6.33    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 47.59/6.33    inference(cnf_transformation,[],[f46])).
% 47.59/6.33  fof(f639,plain,(
% 47.59/6.33    ( ! [X0,X1] : (~r2_hidden(sK2(k1_relat_1(sK1)),X0) | v1_relat_1(sK4(X0,X1))) )),
% 47.59/6.33    inference(superposition,[],[f632,f73])).
% 47.59/6.33  fof(f1976,plain,(
% 47.59/6.33    ( ! [X8,X7] : (k2_xboole_0(k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X7),X8)),k4_xboole_0(X8,k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X7),X8)))) = X8) )),
% 47.59/6.33    inference(resolution,[],[f943,f72])).
% 47.59/6.33  fof(f943,plain,(
% 47.59/6.33    ( ! [X8,X7] : (r1_tarski(k1_relat_1(k7_relat_1(sK4(sK2(k1_relat_1(sK1)),X7),X8)),X8)) )),
% 47.59/6.33    inference(resolution,[],[f938,f68])).
% 47.59/6.33  fof(f28342,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (r2_hidden(X0,sK2(X1)) | k1_relat_1(sK4(X0,X2)) = X2) )),
% 47.59/6.33    inference(superposition,[],[f28323,f77])).
% 47.59/6.33  fof(f28323,plain,(
% 47.59/6.33    ( ! [X12] : (r2_hidden(k1_xboole_0,sK2(X12))) )),
% 47.59/6.33    inference(superposition,[],[f28259,f5089])).
% 47.59/6.33  fof(f28259,plain,(
% 47.59/6.33    ( ! [X24,X23] : (r2_hidden(k1_xboole_0,sK2(k2_xboole_0(X23,X24)))) )),
% 47.59/6.33    inference(resolution,[],[f28046,f55])).
% 47.59/6.33  fof(f28046,plain,(
% 47.59/6.33    ( ! [X10,X8,X9] : (~r1_tarski(X8,k1_relat_1(k7_relat_1(sK1,X10))) | r2_hidden(X8,sK2(k2_xboole_0(X9,X10)))) )),
% 47.59/6.33    inference(resolution,[],[f28023,f60])).
% 47.59/6.33  fof(f28023,plain,(
% 47.59/6.33    ( ! [X0,X1] : (r2_hidden(k1_relat_1(k7_relat_1(sK1,X0)),sK2(k2_xboole_0(X1,X0)))) )),
% 47.59/6.33    inference(resolution,[],[f158,f59])).
% 47.59/6.33  fof(f158,plain,(
% 47.59/6.33    ( ! [X8,X7,X9] : (~r2_hidden(k2_xboole_0(X9,X7),sK2(X8)) | r2_hidden(k1_relat_1(k7_relat_1(sK1,X7)),sK2(X8))) )),
% 47.59/6.33    inference(resolution,[],[f120,f60])).
% 47.59/6.33  fof(f120,plain,(
% 47.59/6.33    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k2_xboole_0(X2,X1))) )),
% 47.59/6.33    inference(resolution,[],[f100,f82])).
% 47.59/6.33  fof(f82,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f39])).
% 47.59/6.33  fof(f39,plain,(
% 47.59/6.33    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 47.59/6.33    inference(ennf_transformation,[],[f4])).
% 47.59/6.33  fof(f4,axiom,(
% 47.59/6.33    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 47.59/6.33  fof(f49606,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(k1_relat_1(sK4(sK2(X0),X1)),X2)) )),
% 47.59/6.33    inference(forward_demodulation,[],[f49605,f32608])).
% 47.59/6.33  fof(f49605,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k1_relat_1(sK4(sK2(X0),X1)) | ~r1_tarski(k1_relat_1(sK4(sK2(X0),X1)),X2)) )),
% 47.59/6.33    inference(subsumption_resolution,[],[f49540,f11874])).
% 47.59/6.33  fof(f11874,plain,(
% 47.59/6.33    ( ! [X2,X3] : (v1_relat_1(sK4(sK2(X2),X3))) )),
% 47.59/6.33    inference(condensation,[],[f11591])).
% 47.59/6.33  fof(f11591,plain,(
% 47.59/6.33    ( ! [X2,X0,X3,X1] : (v1_relat_1(sK4(sK2(X0),X1)) | v1_relat_1(sK4(sK2(X2),X3))) )),
% 47.59/6.33    inference(resolution,[],[f11223,f10948])).
% 47.59/6.33  fof(f10948,plain,(
% 47.59/6.33    ( ! [X41,X42,X40] : (r2_hidden(X40,X41) | v1_relat_1(sK4(sK2(X40),X42))) )),
% 47.59/6.33    inference(resolution,[],[f10448,f59])).
% 47.59/6.33  fof(f10448,plain,(
% 47.59/6.33    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,X0) | r2_hidden(X1,X2) | v1_relat_1(sK4(X0,X3))) )),
% 47.59/6.33    inference(superposition,[],[f10436,f73])).
% 47.59/6.33  fof(f11223,plain,(
% 47.59/6.33    ( ! [X14,X15,X13] : (~r2_hidden(X15,X13) | v1_relat_1(sK4(sK2(X13),X14))) )),
% 47.59/6.33    inference(resolution,[],[f10948,f71])).
% 47.59/6.33  fof(f49540,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k1_relat_1(sK4(sK2(X0),X1)) | ~r1_tarski(k1_relat_1(sK4(sK2(X0),X1)),X2) | ~v1_relat_1(sK4(sK2(X0),X1))) )),
% 47.59/6.33    inference(superposition,[],[f32620,f70])).
% 47.59/6.33  fof(f32620,plain,(
% 47.59/6.33    ( ! [X14,X15,X16] : (k3_xboole_0(X15,X16) = k1_relat_1(k7_relat_1(sK4(sK2(X14),X15),X16))) )),
% 47.59/6.33    inference(backward_demodulation,[],[f11880,f32608])).
% 47.59/6.33  fof(f11880,plain,(
% 47.59/6.33    ( ! [X14,X15,X16] : (k1_relat_1(k7_relat_1(sK4(sK2(X14),X15),X16)) = k3_xboole_0(k1_relat_1(sK4(sK2(X14),X15)),X16)) )),
% 47.59/6.33    inference(resolution,[],[f11874,f69])).
% 47.59/6.33  fof(f1125,plain,(
% 47.59/6.33    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(X0,X1)) = k9_relat_1(sK1,k3_xboole_0(X0,X1))) )),
% 47.59/6.33    inference(resolution,[],[f98,f64])).
% 47.59/6.33  fof(f64,plain,(
% 47.59/6.33    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f5])).
% 47.59/6.33  fof(f5,axiom,(
% 47.59/6.33    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 47.59/6.33  fof(f98,plain,(
% 47.59/6.33    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k7_relat_1(sK1,X0),X1) = k9_relat_1(sK1,X1)) )),
% 47.59/6.33    inference(resolution,[],[f52,f58])).
% 47.59/6.33  fof(f58,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f26])).
% 47.59/6.33  fof(f26,plain,(
% 47.59/6.33    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 47.59/6.33    inference(ennf_transformation,[],[f12])).
% 47.59/6.33  fof(f12,axiom,(
% 47.59/6.33    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 47.59/6.33  fof(f57093,plain,(
% 47.59/6.33    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 47.59/6.33    inference(superposition,[],[f110,f55444])).
% 47.59/6.33  fof(f55444,plain,(
% 47.59/6.33    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 47.59/6.33    inference(superposition,[],[f49694,f190])).
% 47.59/6.33  fof(f190,plain,(
% 47.59/6.33    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k1_relat_1(sK1))) )),
% 47.59/6.33    inference(superposition,[],[f101,f65])).
% 47.59/6.33  fof(f65,plain,(
% 47.59/6.33    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f2])).
% 47.59/6.33  fof(f2,axiom,(
% 47.59/6.33    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 47.59/6.33  fof(f101,plain,(
% 47.59/6.33    ( ! [X4] : (k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(sK1),X4)) )),
% 47.59/6.33    inference(resolution,[],[f52,f69])).
% 47.59/6.33  fof(f110,plain,(
% 47.59/6.33    ( ! [X1] : (k9_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1))) = k2_relat_1(k7_relat_1(sK1,X1))) )),
% 47.59/6.33    inference(resolution,[],[f99,f57])).
% 47.59/6.33  fof(f57,plain,(
% 47.59/6.33    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f25])).
% 47.59/6.33  fof(f25,plain,(
% 47.59/6.33    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 47.59/6.33    inference(ennf_transformation,[],[f11])).
% 47.59/6.33  fof(f11,axiom,(
% 47.59/6.33    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 47.59/6.33  fof(f99,plain,(
% 47.59/6.33    ( ! [X2] : (v1_relat_1(k7_relat_1(sK1,X2))) )),
% 47.59/6.33    inference(resolution,[],[f52,f67])).
% 47.59/6.33  fof(f67,plain,(
% 47.59/6.33    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f29])).
% 47.59/6.33  fof(f29,plain,(
% 47.59/6.33    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 47.59/6.33    inference(ennf_transformation,[],[f10])).
% 47.59/6.33  fof(f10,axiom,(
% 47.59/6.33    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 47.59/6.33  fof(f57136,plain,(
% 47.59/6.33    r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))),
% 47.59/6.33    inference(superposition,[],[f8732,f55444])).
% 47.59/6.33  fof(f8732,plain,(
% 47.59/6.33    ( ! [X88] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X88)),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X88))))) )),
% 47.59/6.33    inference(superposition,[],[f5076,f367])).
% 47.59/6.33  fof(f367,plain,(
% 47.59/6.33    ( ! [X4] : (k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4))))) )),
% 47.59/6.33    inference(subsumption_resolution,[],[f364,f99])).
% 47.59/6.33  fof(f364,plain,(
% 47.59/6.33    ( ! [X4] : (k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4)))) | ~v1_relat_1(k7_relat_1(sK1,X4))) )),
% 47.59/6.33    inference(superposition,[],[f103,f56])).
% 47.59/6.33  fof(f56,plain,(
% 47.59/6.33    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f24])).
% 47.59/6.33  fof(f24,plain,(
% 47.59/6.33    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 47.59/6.33    inference(ennf_transformation,[],[f13])).
% 47.59/6.33  fof(f13,axiom,(
% 47.59/6.33    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 47.59/6.33  fof(f103,plain,(
% 47.59/6.33    ( ! [X6,X7] : (k10_relat_1(k7_relat_1(sK1,X6),X7) = k3_xboole_0(X6,k10_relat_1(sK1,X7))) )),
% 47.59/6.33    inference(resolution,[],[f52,f81])).
% 47.59/6.33  fof(f81,plain,(
% 47.59/6.33    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 47.59/6.33    inference(cnf_transformation,[],[f38])).
% 47.59/6.33  fof(f38,plain,(
% 47.59/6.33    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 47.59/6.33    inference(ennf_transformation,[],[f17])).
% 47.59/6.33  fof(f17,axiom,(
% 47.59/6.33    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 47.59/6.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 47.59/6.33  fof(f5076,plain,(
% 47.59/6.33    ( ! [X8,X7] : (r1_tarski(k3_xboole_0(X7,X8),X8)) )),
% 47.59/6.33    inference(backward_demodulation,[],[f951,f5069])).
% 47.59/6.33  fof(f5069,plain,(
% 47.59/6.33    ( ! [X10,X9] : (k1_relat_1(k7_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X9),X10)) = k3_xboole_0(X9,X10)) )),
% 47.59/6.33    inference(backward_demodulation,[],[f952,f5056])).
% 47.59/6.33  fof(f5056,plain,(
% 47.59/6.33    ( ! [X16] : (k1_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X16)) = X16) )),
% 47.59/6.33    inference(resolution,[],[f640,f59])).
% 47.59/6.33  fof(f952,plain,(
% 47.59/6.33    ( ! [X10,X9] : (k1_relat_1(k7_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X9),X10)) = k3_xboole_0(k1_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X9)),X10)) )),
% 47.59/6.33    inference(resolution,[],[f931,f69])).
% 47.59/6.33  fof(f931,plain,(
% 47.59/6.33    ( ! [X16] : (v1_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X16))) )),
% 47.59/6.33    inference(resolution,[],[f639,f59])).
% 47.59/6.33  fof(f951,plain,(
% 47.59/6.33    ( ! [X8,X7] : (r1_tarski(k1_relat_1(k7_relat_1(sK4(sK2(sK2(k1_relat_1(sK1))),X7),X8)),X8)) )),
% 47.59/6.33    inference(resolution,[],[f931,f68])).
% 47.59/6.33  % SZS output end Proof for theBenchmark
% 47.59/6.33  % (17880)------------------------------
% 47.59/6.33  % (17880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 47.59/6.33  % (17880)Termination reason: Refutation
% 47.59/6.33  
% 47.59/6.33  % (17880)Memory used [KB]: 37867
% 47.59/6.33  % (17880)Time elapsed: 5.824 s
% 47.59/6.33  % (17880)------------------------------
% 47.59/6.33  % (17880)------------------------------
% 47.59/6.34  % (17856)Success in time 5.979 s
%------------------------------------------------------------------------------
