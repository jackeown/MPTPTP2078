%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t141_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:30 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 467 expanded)
%              Number of leaves         :   12 ( 148 expanded)
%              Depth                    :   14
%              Number of atoms          :  365 (3231 expanded)
%              Number of equality atoms :   92 ( 894 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(subsumption_resolution,[],[f246,f245])).

fof(f245,plain,(
    r2_hidden(sK2(sK0,sK0),sK0) ),
    inference(resolution,[],[f244,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t141_funct_2.p',d3_tarski)).

fof(f244,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f243,f128])).

fof(f128,plain,(
    k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) = sK0 ),
    inference(forward_demodulation,[],[f110,f109])).

fof(f109,plain,(
    sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) = sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(resolution,[],[f94,f91])).

fof(f91,plain,(
    ! [X6,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK6(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
              & k1_relat_1(sK7(X0,X1,X2)) = X0
              & sK6(X0,X1,X2) = sK7(X0,X1,X2)
              & v1_funct_1(sK7(X0,X1,X2))
              & v1_relat_1(sK7(X0,X1,X2)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
                & k1_relat_1(sK8(X0,X1,X6)) = X0
                & sK8(X0,X1,X6) = X6
                & v1_funct_1(sK8(X0,X1,X6))
                & v1_relat_1(sK8(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f43,f46,f45,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK6(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK6(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
        & k1_relat_1(sK7(X0,X1,X2)) = X0
        & sK7(X0,X1,X2) = X3
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
        & k1_relat_1(sK8(X0,X1,X6)) = X0
        & sK8(X0,X1,X6) = X6
        & v1_funct_1(sK8(X0,X1,X6))
        & v1_relat_1(sK8(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t141_funct_2.p',d2_funct_2)).

fof(f94,plain,(
    r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f48,f50])).

fof(f48,plain,(
    ~ r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ~ r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).

fof(f30,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))
   => ~ r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t141_funct_2.p',t141_funct_2)).

fof(f110,plain,(
    k1_relat_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) = sK0 ),
    inference(resolution,[],[f94,f90])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f243,plain,(
    ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f242,f127])).

fof(f127,plain,(
    v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f109,f107])).

fof(f107,plain,(
    v1_relat_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(resolution,[],[f94,f93])).

fof(f93,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f242,plain,
    ( ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f241,f126])).

fof(f126,plain,(
    v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f109,f108])).

fof(f108,plain,(
    v1_funct_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(resolution,[],[f94,f92])).

fof(f92,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f241,plain,
    ( ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))
    | ~ v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f228,f129])).

fof(f129,plain,(
    r1_tarski(k2_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK1) ),
    inference(forward_demodulation,[],[f111,f109])).

fof(f111,plain,(
    r1_tarski(k2_relat_1(sK8(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),sK1) ),
    inference(resolution,[],[f94,f89])).

fof(f89,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f228,plain,
    ( ~ r1_tarski(k2_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK1)
    | ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))
    | ~ v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(resolution,[],[f95,f79])).

fof(f79,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(X7,k4_partfun1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ r1_tarski(k1_relat_1(X7),X0)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ r1_tarski(k1_relat_1(X7),X0)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ r1_tarski(k1_relat_1(X7),X0)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | ~ r1_tarski(k1_relat_1(X4),X0)
                | sK3(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1)
              & r1_tarski(k1_relat_1(sK4(X0,X1,X2)),X0)
              & sK3(X0,X1,X2) = sK4(X0,X1,X2)
              & v1_funct_1(sK4(X0,X1,X2))
              & v1_relat_1(sK4(X0,X1,X2)) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | ~ r1_tarski(k1_relat_1(X7),X0)
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)
                & r1_tarski(k1_relat_1(sK5(X0,X1,X6)),X0)
                & sK5(X0,X1,X6) = X6
                & v1_funct_1(sK5(X0,X1,X6))
                & v1_relat_1(sK5(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f40,f39,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | ~ r1_tarski(k1_relat_1(X4),X0)
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & r1_tarski(k1_relat_1(X5),X0)
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | ~ r1_tarski(k1_relat_1(X4),X0)
              | sK3(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & r1_tarski(k1_relat_1(X5),X0)
              & sK3(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & r1_tarski(k1_relat_1(X5),X0)
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1)
        & r1_tarski(k1_relat_1(sK4(X0,X1,X2)),X0)
        & sK4(X0,X1,X2) = X3
        & v1_funct_1(sK4(X0,X1,X2))
        & v1_relat_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & r1_tarski(k1_relat_1(X8),X0)
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)
        & r1_tarski(k1_relat_1(sK5(X0,X1,X6)),X0)
        & sK5(X0,X1,X6) = X6
        & v1_funct_1(sK5(X0,X1,X6))
        & v1_relat_1(sK5(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & r1_tarski(k1_relat_1(X5),X0)
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | ~ r1_tarski(k1_relat_1(X7),X0)
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & r1_tarski(k1_relat_1(X8),X0)
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & r1_tarski(k1_relat_1(X4),X0)
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & r1_tarski(k1_relat_1(X4),X0)
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & r1_tarski(k1_relat_1(X4),X0)
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t141_funct_2.p',d5_partfun1)).

fof(f95,plain,(
    ~ r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k4_partfun1(sK0,sK1)) ),
    inference(resolution,[],[f48,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f246,plain,(
    ~ r2_hidden(sK2(sK0,sK0),sK0) ),
    inference(resolution,[],[f244,f51])).
%------------------------------------------------------------------------------
