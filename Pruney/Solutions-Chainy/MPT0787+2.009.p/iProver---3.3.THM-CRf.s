%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:32 EST 2020

% Result     : Theorem 19.52s
% Output     : CNFRefutation 19.52s
% Verified   : 
% Statistics : Number of formulae       :  264 (19273 expanded)
%              Number of clauses        :  174 (4948 expanded)
%              Number of leaves         :   22 (3420 expanded)
%              Depth                    :   41
%              Number of atoms          : 1092 (120512 expanded)
%              Number of equality atoms :  356 (15128 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
          | sK1(X0,X1,X2) = X1
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
            & sK1(X0,X1,X2) != X1 )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
                | sK1(X0,X1,X2) = X1
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
                  & sK1(X0,X1,X2) != X1 )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
        | ~ r2_hidden(k4_tarski(sK9,sK10),sK11) )
      & ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
        | r2_hidden(k4_tarski(sK9,sK10),sK11) )
      & r2_hidden(sK10,k3_relat_1(sK11))
      & r2_hidden(sK9,k3_relat_1(sK11))
      & v2_wellord1(sK11)
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
      | ~ r2_hidden(k4_tarski(sK9,sK10),sK11) )
    & ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
      | r2_hidden(k4_tarski(sK9,sK10),sK11) )
    & r2_hidden(sK10,k3_relat_1(sK11))
    & r2_hidden(sK9,k3_relat_1(sK11))
    & v2_wellord1(sK11)
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f58,f59])).

fof(f99,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK5(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f48])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK4(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK4(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK4(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK4(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,sK4(X0,X1))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
        & sK2(X0) != sK3(X0)
        & r2_hidden(sK3(X0),k3_relat_1(X0))
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
            & sK2(X0) != sK3(X0)
            & r2_hidden(sK3(X0),k3_relat_1(X0))
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).

fof(f79,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f51])).

fof(f55,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X3),X1) )
     => ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(k4_tarski(sK8(X0,X1),X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,X0)
              & r2_hidden(k4_tarski(X4,X3),X1) )
          & r2_hidden(X3,X0) )
     => ( ? [X4] :
            ( ~ r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,sK7(X0,X1)),X1) )
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_wellord1(X1,X2) = X0
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK6(X0,X1)) = X0
        & r2_hidden(sK6(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_wellord1(X1,sK6(X0,X1)) = X0
            & r2_hidden(sK6(X0,X1),k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ( ~ r2_hidden(sK8(X0,X1),X0)
            & r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X1)
            & r2_hidden(sK7(X0,X1),X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f55,f54,f53])).

fof(f92,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k1_wellord1(X1,X7) != X0
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X6,X7,X5,X1] :
      ( r2_hidden(X6,k1_wellord1(X1,X7))
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,k1_wellord1(X1,X7))
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f92])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK11) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f60])).

fof(f102,plain,(
    r2_hidden(sK10,k3_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f60])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f107,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f108,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f103,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | r2_hidden(k4_tarski(sK9,sK10),sK11) ),
    inference(cnf_transformation,[],[f60])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK4(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK4(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
    | ~ v1_relat_1(X0)
    | k1_wellord1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_43,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_991,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
    | k1_wellord1(X0,X1) = X2
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_43])).

cnf(c_992,plain,
    ( r2_hidden(sK1(sK11,X0,X1),X1)
    | r2_hidden(k4_tarski(sK1(sK11,X0,X1),X0),sK11)
    | k1_wellord1(sK11,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_3482,plain,
    ( k1_wellord1(sK11,X0) = X1
    | r2_hidden(sK1(sK11,X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK1(sK11,X0,X1),X0),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_3,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_947,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_43])).

cnf(c_948,plain,
    ( r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X1,X0),sK11) ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_3485,plain,
    ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_5594,plain,
    ( k1_wellord1(sK11,X0) = X1
    | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r2_hidden(sK1(sK11,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3482,c_3485])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_910,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_43])).

cnf(c_911,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_3488,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_8118,plain,
    ( k1_wellord1(sK11,X0) = k1_wellord1(sK11,X1)
    | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(sK1(sK11,X0,k1_wellord1(sK11,X1)),X1),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_5594,c_3488])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3507,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13282,plain,
    ( k1_wellord1(sK11,X0) = k1_wellord1(sK11,X1)
    | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(sK1(sK11,X0,k1_wellord1(sK11,X1)),X1),X2) = iProver_top
    | r1_tarski(sK11,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8118,c_3507])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3506,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_62876,plain,
    ( k1_wellord1(sK11,X0) = k1_wellord1(sK11,X1)
    | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r1_tarski(X2,k4_tarski(sK1(sK11,X0,k1_wellord1(sK11,X1)),X1)) != iProver_top
    | r1_tarski(sK11,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13282,c_3506])).

cnf(c_29,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_957,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_43])).

cnf(c_958,plain,
    ( r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_959,plain,
    ( r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_3713,plain,
    ( r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(sK9,X0),sK11) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_3714,plain,
    ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3713])).

cnf(c_2847,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4510,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2847])).

cnf(c_5284,plain,
    ( r2_hidden(k4_tarski(sK9,X0),sK11)
    | ~ r2_hidden(sK9,k1_wellord1(sK11,X0)) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_5285,plain,
    ( r2_hidden(k4_tarski(sK9,X0),sK11) = iProver_top
    | r2_hidden(sK9,k1_wellord1(sK11,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5284])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3508,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4851,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X0),sK11) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3488])).

cnf(c_5946,plain,
    ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4851,c_3485])).

cnf(c_28,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,negated_conjecture,
    ( v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_565,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK11 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_42])).

cnf(c_566,plain,
    ( r2_hidden(sK5(sK11,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK11))
    | ~ v1_relat_1(sK11)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_570,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK11))
    | r2_hidden(sK5(sK11,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_43])).

cnf(c_571,plain,
    ( r2_hidden(sK5(sK11,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK11))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_3501,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK5(sK11,X0),X0) = iProver_top
    | r1_tarski(X0,k3_relat_1(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_5405,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,sK5(sK11,X0)) != iProver_top
    | r1_tarski(X0,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3501,c_3506])).

cnf(c_8067,plain,
    ( k1_wellord1(sK11,X0) = k1_xboole_0
    | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5946,c_5405])).

cnf(c_2850,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3623,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_wellord1(sK11,X3))
    | X2 != X0
    | k1_wellord1(sK11,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_11971,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1))
    | ~ r2_hidden(sK9,k1_xboole_0)
    | X0 != sK9
    | k1_wellord1(sK11,X1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3623])).

cnf(c_39312,plain,
    ( r2_hidden(sK9,k1_wellord1(sK11,X0))
    | ~ r2_hidden(sK9,k1_xboole_0)
    | k1_wellord1(sK11,X0) != k1_xboole_0
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_11971])).

cnf(c_39313,plain,
    ( k1_wellord1(sK11,X0) != k1_xboole_0
    | sK9 != sK9
    | r2_hidden(sK9,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(sK9,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39312])).

cnf(c_24,plain,
    ( r2_hidden(X0,sK4(X1,X2))
    | ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_859,plain,
    ( r2_hidden(X0,sK4(X1,X2))
    | ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_43])).

cnf(c_860,plain,
    ( r2_hidden(X0,sK4(sK11,X1))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_3491,plain,
    ( r2_hidden(X0,sK4(sK11,X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3509,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4166,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3509])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_874,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_43])).

cnf(c_875,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v6_relat_2(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_874])).

cnf(c_14,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_116,plain,
    ( v6_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_879,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_875,c_43,c_42,c_116])).

cnf(c_880,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_879])).

cnf(c_3490,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_920,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_43])).

cnf(c_921,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_3487,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_5821,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(sK11,X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_3490,c_3487])).

cnf(c_36,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X3,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_621,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X3,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_42])).

cnf(c_622,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(X2,k1_wellord1(sK11,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r1_tarski(k1_wellord1(sK11,X1),k3_relat_1(sK11))
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_624,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,X1),k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(X2,k1_wellord1(sK11,X1))
    | ~ r2_hidden(X0,k1_wellord1(sK11,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_43])).

cnf(c_625,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(X2,k1_wellord1(sK11,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r1_tarski(k1_wellord1(sK11,X1),k3_relat_1(sK11)) ),
    inference(renaming,[status(thm)],[c_624])).

cnf(c_1056,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(X2,k1_wellord1(sK11,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X2,X0),sK11) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_958,c_625])).

cnf(c_3480,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1)) != iProver_top
    | r2_hidden(X2,k1_wellord1(sK11,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_4158,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK0(k1_wellord1(sK11,X1),X2)),sK11) != iProver_top
    | r1_tarski(k1_wellord1(sK11,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3480])).

cnf(c_7186,plain,
    ( sK0(k1_wellord1(sK11,X0),X1) = X2
    | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
    | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) != iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3490,c_4158])).

cnf(c_4,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_935,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_43])).

cnf(c_936,plain,
    ( r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_3486,plain,
    ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_5944,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4851,c_3486])).

cnf(c_49706,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | sK0(k1_wellord1(sK11,X0),X1) = X2
    | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7186,c_5944,c_5946])).

cnf(c_49707,plain,
    ( sK0(k1_wellord1(sK11,X0),X1) = X2
    | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_49706])).

cnf(c_49715,plain,
    ( sK0(k1_wellord1(sK11,X0),X1) = X2
    | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k1_wellord1(sK11,X2)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_49707,c_3487])).

cnf(c_56702,plain,
    ( sK0(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = X1
    | r2_hidden(X1,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49715,c_3509])).

cnf(c_38,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
    | ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3505,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_76114,plain,
    ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
    | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56702,c_3505])).

cnf(c_41,negated_conjecture,
    ( r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_46,plain,
    ( r2_hidden(sK9,k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(sK10,k3_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_47,plain,
    ( r2_hidden(sK10,k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_901,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_43])).

cnf(c_902,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X0)) ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_5324,plain,
    ( ~ r2_hidden(sK9,k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_5325,plain,
    ( r2_hidden(sK9,k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5324])).

cnf(c_3653,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,sK9))
    | r2_hidden(X1,k1_wellord1(sK11,sK9))
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_11330,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,sK9))
    | ~ r2_hidden(k4_tarski(sK9,X0),sK11)
    | r2_hidden(sK9,k1_wellord1(sK11,sK9))
    | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_3653])).

cnf(c_22235,plain,
    ( ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | r2_hidden(sK9,k1_wellord1(sK11,sK9))
    | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_11330])).

cnf(c_22236,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top
    | r2_hidden(sK9,k1_wellord1(sK11,sK9)) = iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22235])).

cnf(c_76200,plain,
    ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
    | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_76114,c_46,c_47,c_5325,c_22236])).

cnf(c_76212,plain,
    ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
    | sK10 = sK9
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5821,c_76200])).

cnf(c_39,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK10),sK11)
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_5203,plain,
    ( ~ r2_hidden(sK10,k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_3586,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_wellord1(sK11,X0))
    | ~ r1_tarski(X1,k1_wellord1(sK11,X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5213,plain,
    ( ~ r2_hidden(sK10,k1_wellord1(sK11,X0))
    | r2_hidden(sK10,k1_wellord1(sK11,sK10))
    | ~ r1_tarski(k1_wellord1(sK11,X0),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_21859,plain,
    ( r2_hidden(sK10,k1_wellord1(sK11,sK10))
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_5213])).

cnf(c_76202,plain,
    ( ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
    | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_76200])).

cnf(c_76217,plain,
    ( r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | ~ r2_hidden(sK10,k3_relat_1(sK11))
    | ~ r2_hidden(sK9,k3_relat_1(sK11))
    | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
    | sK10 = sK9 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_76212])).

cnf(c_76278,plain,
    ( sK10 = sK9
    | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_76212,c_41,c_40,c_39,c_5203,c_21859,c_76202,c_76217])).

cnf(c_76279,plain,
    ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
    | sK10 = sK9 ),
    inference(renaming,[status(thm)],[c_76278])).

cnf(c_76296,plain,
    ( sK10 = sK9
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_76279,c_3508])).

cnf(c_48,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),sK11) = iProver_top
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_77083,plain,
    ( sK10 = sK9
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_76296,c_46,c_48,c_5325,c_22236])).

cnf(c_77087,plain,
    ( sK10 = sK9
    | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_77083,c_3505])).

cnf(c_77135,plain,
    ( sK10 = sK9
    | r2_hidden(sK9,sK4(sK11,sK10)) = iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_77087])).

cnf(c_5204,plain,
    ( r2_hidden(sK10,k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5203])).

cnf(c_21860,plain,
    ( r2_hidden(sK10,k1_wellord1(sK11,sK10)) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21859])).

cnf(c_77137,plain,
    ( sK10 = sK9
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5821,c_77087])).

cnf(c_77477,plain,
    ( sK10 = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_77135,c_46,c_47,c_5204,c_21860,c_77083,c_77137])).

cnf(c_77542,plain,
    ( r2_hidden(k4_tarski(sK9,sK9),sK11) != iProver_top
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_77477,c_3505])).

cnf(c_78108,plain,
    ( r2_hidden(k4_tarski(sK9,sK9),sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_4166,c_77542])).

cnf(c_78118,plain,
    ( r2_hidden(sK9,sK4(sK11,sK9)) = iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_78108])).

cnf(c_3631,plain,
    ( r2_hidden(k4_tarski(sK9,X0),sK11)
    | r2_hidden(sK9,sK4(sK11,X0))
    | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_4416,plain,
    ( r2_hidden(k4_tarski(sK9,sK9),sK11)
    | r2_hidden(sK9,sK4(sK11,sK9))
    | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_3631])).

cnf(c_4419,plain,
    ( r2_hidden(k4_tarski(sK9,sK9),sK11) = iProver_top
    | r2_hidden(sK9,sK4(sK11,sK9)) = iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4416])).

cnf(c_78184,plain,
    ( r2_hidden(sK9,sK4(sK11,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_78118,c_46,c_4419,c_78108])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK5(X2,X1),X0),X2)
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_597,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK5(X2,X1),X0),X2)
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | sK11 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_42])).

cnf(c_598,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK5(sK11,X1),X0),sK11)
    | ~ r1_tarski(X1,k3_relat_1(sK11))
    | ~ v1_relat_1(sK11)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_602,plain,
    ( ~ r1_tarski(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(sK5(sK11,X1),X0),sK11)
    | ~ r2_hidden(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_43])).

cnf(c_603,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK5(sK11,X1),X0),sK11)
    | ~ r1_tarski(X1,k3_relat_1(sK11))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_602])).

cnf(c_3500,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK11,X0),X1),sK11) = iProver_top
    | r1_tarski(X0,k3_relat_1(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,sK4(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_847,plain,
    ( ~ r2_hidden(X0,sK4(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_43])).

cnf(c_848,plain,
    ( ~ r2_hidden(X0,sK4(sK11,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_3492,plain,
    ( r2_hidden(X0,sK4(sK11,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_5408,plain,
    ( sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(k4_tarski(sK5(sK11,sK4(sK11,X0)),X0),sK11) != iProver_top
    | r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3501,c_3492])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,sK4(X1,X2))
    | r2_hidden(X0,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_835,plain,
    ( ~ r2_hidden(X0,sK4(X1,X2))
    | r2_hidden(X0,k3_relat_1(X1))
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_43])).

cnf(c_836,plain,
    ( ~ r2_hidden(X0,sK4(sK11,X1))
    | r2_hidden(X0,k3_relat_1(sK11)) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_3493,plain,
    ( r2_hidden(X0,sK4(sK11,X1)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_4613,plain,
    ( r2_hidden(sK0(sK4(sK11,X0),X1),k3_relat_1(sK11)) = iProver_top
    | r1_tarski(sK4(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3493])).

cnf(c_5302,plain,
    ( r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4613,c_3509])).

cnf(c_7733,plain,
    ( r2_hidden(k4_tarski(sK5(sK11,sK4(sK11,X0)),X0),sK11) != iProver_top
    | sK4(sK11,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5408,c_5302])).

cnf(c_7734,plain,
    ( sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(k4_tarski(sK5(sK11,sK4(sK11,X0)),X0),sK11) != iProver_top ),
    inference(renaming,[status(thm)],[c_7733])).

cnf(c_7739,plain,
    ( sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(X0,sK4(sK11,X0)) != iProver_top
    | r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_7734])).

cnf(c_7753,plain,
    ( r2_hidden(X0,sK4(sK11,X0)) != iProver_top
    | sK4(sK11,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7739,c_5302])).

cnf(c_7754,plain,
    ( sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(X0,sK4(sK11,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7753])).

cnf(c_78192,plain,
    ( sK4(sK11,sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_78184,c_7754])).

cnf(c_78193,plain,
    ( r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_78192,c_78184])).

cnf(c_78206,plain,
    ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62876,c_959,c_3714,c_4510,c_5285,c_8067,c_39313,c_78193])).

cnf(c_3484,plain,
    ( r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_7742,plain,
    ( sK5(sK11,sK4(sK11,X0)) = X0
    | sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(sK5(sK11,sK4(sK11,X0)),k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(sK11,sK4(sK11,X0))),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_3490,c_7734])).

cnf(c_5409,plain,
    ( sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(sK5(sK11,sK4(sK11,X0)),k3_relat_1(sK11)) = iProver_top
    | r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3501,c_3493])).

cnf(c_61479,plain,
    ( r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | sK4(sK11,X0) = k1_xboole_0
    | sK5(sK11,sK4(sK11,X0)) = X0
    | r2_hidden(k4_tarski(X0,sK5(sK11,sK4(sK11,X0))),sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7742,c_5302,c_5409])).

cnf(c_61480,plain,
    ( sK5(sK11,sK4(sK11,X0)) = X0
    | sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(sK11,sK4(sK11,X0))),sK11) = iProver_top ),
    inference(renaming,[status(thm)],[c_61479])).

cnf(c_61491,plain,
    ( sK5(sK11,sK4(sK11,X0)) = X0
    | sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(X0,k1_wellord1(sK11,sK5(sK11,sK4(sK11,X0)))) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_61480,c_3487])).

cnf(c_61922,plain,
    ( sK5(sK11,sK4(sK11,X0)) = X0
    | sK4(sK11,X0) = k1_xboole_0
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r1_tarski(k1_wellord1(sK11,sK5(sK11,sK4(sK11,X0))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_61491,c_3506])).

cnf(c_66927,plain,
    ( sK5(sK11,sK4(sK11,k3_relat_1(sK11))) = k3_relat_1(sK11)
    | sK4(sK11,k3_relat_1(sK11)) = k1_xboole_0
    | r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3484,c_61922])).

cnf(c_5025,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(sK11),X0),X0)
    | r1_tarski(k3_relat_1(sK11),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8192,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11))
    | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_5025])).

cnf(c_8194,plain,
    ( r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11)) != iProver_top
    | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8192])).

cnf(c_5026,plain,
    ( r2_hidden(sK0(k3_relat_1(sK11),X0),k3_relat_1(sK11))
    | r1_tarski(k3_relat_1(sK11),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8193,plain,
    ( r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11))
    | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_5026])).

cnf(c_8196,plain,
    ( r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11)) = iProver_top
    | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8193])).

cnf(c_4214,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r1_tarski(k3_relat_1(sK11),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_17464,plain,
    ( ~ r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11))
    | ~ r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_4214])).

cnf(c_17469,plain,
    ( r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top
    | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17464])).

cnf(c_67141,plain,
    ( r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_66927,c_8194,c_8196,c_17469])).

cnf(c_78220,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_78206,c_67141])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:37:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.52/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.52/2.98  
% 19.52/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.52/2.98  
% 19.52/2.98  ------  iProver source info
% 19.52/2.98  
% 19.52/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.52/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.52/2.98  git: non_committed_changes: false
% 19.52/2.98  git: last_make_outside_of_git: false
% 19.52/2.98  
% 19.52/2.98  ------ 
% 19.52/2.98  
% 19.52/2.98  ------ Input Options
% 19.52/2.98  
% 19.52/2.98  --out_options                           all
% 19.52/2.98  --tptp_safe_out                         true
% 19.52/2.98  --problem_path                          ""
% 19.52/2.98  --include_path                          ""
% 19.52/2.98  --clausifier                            res/vclausify_rel
% 19.52/2.98  --clausifier_options                    ""
% 19.52/2.98  --stdin                                 false
% 19.52/2.98  --stats_out                             all
% 19.52/2.98  
% 19.52/2.98  ------ General Options
% 19.52/2.98  
% 19.52/2.98  --fof                                   false
% 19.52/2.98  --time_out_real                         305.
% 19.52/2.98  --time_out_virtual                      -1.
% 19.52/2.98  --symbol_type_check                     false
% 19.52/2.98  --clausify_out                          false
% 19.52/2.98  --sig_cnt_out                           false
% 19.52/2.98  --trig_cnt_out                          false
% 19.52/2.98  --trig_cnt_out_tolerance                1.
% 19.52/2.98  --trig_cnt_out_sk_spl                   false
% 19.52/2.98  --abstr_cl_out                          false
% 19.52/2.98  
% 19.52/2.98  ------ Global Options
% 19.52/2.98  
% 19.52/2.98  --schedule                              default
% 19.52/2.98  --add_important_lit                     false
% 19.52/2.98  --prop_solver_per_cl                    1000
% 19.52/2.98  --min_unsat_core                        false
% 19.52/2.98  --soft_assumptions                      false
% 19.52/2.98  --soft_lemma_size                       3
% 19.52/2.98  --prop_impl_unit_size                   0
% 19.52/2.98  --prop_impl_unit                        []
% 19.52/2.98  --share_sel_clauses                     true
% 19.52/2.98  --reset_solvers                         false
% 19.52/2.98  --bc_imp_inh                            [conj_cone]
% 19.52/2.98  --conj_cone_tolerance                   3.
% 19.52/2.98  --extra_neg_conj                        none
% 19.52/2.98  --large_theory_mode                     true
% 19.52/2.98  --prolific_symb_bound                   200
% 19.52/2.98  --lt_threshold                          2000
% 19.52/2.98  --clause_weak_htbl                      true
% 19.52/2.98  --gc_record_bc_elim                     false
% 19.52/2.98  
% 19.52/2.98  ------ Preprocessing Options
% 19.52/2.98  
% 19.52/2.98  --preprocessing_flag                    true
% 19.52/2.98  --time_out_prep_mult                    0.1
% 19.52/2.98  --splitting_mode                        input
% 19.52/2.98  --splitting_grd                         true
% 19.52/2.98  --splitting_cvd                         false
% 19.52/2.98  --splitting_cvd_svl                     false
% 19.52/2.98  --splitting_nvd                         32
% 19.52/2.98  --sub_typing                            true
% 19.52/2.98  --prep_gs_sim                           true
% 19.52/2.98  --prep_unflatten                        true
% 19.52/2.98  --prep_res_sim                          true
% 19.52/2.98  --prep_upred                            true
% 19.52/2.98  --prep_sem_filter                       exhaustive
% 19.52/2.98  --prep_sem_filter_out                   false
% 19.52/2.98  --pred_elim                             true
% 19.52/2.98  --res_sim_input                         true
% 19.52/2.98  --eq_ax_congr_red                       true
% 19.52/2.98  --pure_diseq_elim                       true
% 19.52/2.98  --brand_transform                       false
% 19.52/2.98  --non_eq_to_eq                          false
% 19.52/2.98  --prep_def_merge                        true
% 19.52/2.98  --prep_def_merge_prop_impl              false
% 19.52/2.98  --prep_def_merge_mbd                    true
% 19.52/2.98  --prep_def_merge_tr_red                 false
% 19.52/2.98  --prep_def_merge_tr_cl                  false
% 19.52/2.98  --smt_preprocessing                     true
% 19.52/2.98  --smt_ac_axioms                         fast
% 19.52/2.98  --preprocessed_out                      false
% 19.52/2.98  --preprocessed_stats                    false
% 19.52/2.98  
% 19.52/2.98  ------ Abstraction refinement Options
% 19.52/2.98  
% 19.52/2.98  --abstr_ref                             []
% 19.52/2.98  --abstr_ref_prep                        false
% 19.52/2.98  --abstr_ref_until_sat                   false
% 19.52/2.98  --abstr_ref_sig_restrict                funpre
% 19.52/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.52/2.98  --abstr_ref_under                       []
% 19.52/2.98  
% 19.52/2.98  ------ SAT Options
% 19.52/2.98  
% 19.52/2.98  --sat_mode                              false
% 19.52/2.98  --sat_fm_restart_options                ""
% 19.52/2.98  --sat_gr_def                            false
% 19.52/2.98  --sat_epr_types                         true
% 19.52/2.98  --sat_non_cyclic_types                  false
% 19.52/2.98  --sat_finite_models                     false
% 19.52/2.98  --sat_fm_lemmas                         false
% 19.52/2.98  --sat_fm_prep                           false
% 19.52/2.98  --sat_fm_uc_incr                        true
% 19.52/2.98  --sat_out_model                         small
% 19.52/2.98  --sat_out_clauses                       false
% 19.52/2.98  
% 19.52/2.98  ------ QBF Options
% 19.52/2.98  
% 19.52/2.98  --qbf_mode                              false
% 19.52/2.98  --qbf_elim_univ                         false
% 19.52/2.98  --qbf_dom_inst                          none
% 19.52/2.98  --qbf_dom_pre_inst                      false
% 19.52/2.98  --qbf_sk_in                             false
% 19.52/2.98  --qbf_pred_elim                         true
% 19.52/2.98  --qbf_split                             512
% 19.52/2.98  
% 19.52/2.98  ------ BMC1 Options
% 19.52/2.98  
% 19.52/2.98  --bmc1_incremental                      false
% 19.52/2.98  --bmc1_axioms                           reachable_all
% 19.52/2.98  --bmc1_min_bound                        0
% 19.52/2.98  --bmc1_max_bound                        -1
% 19.52/2.98  --bmc1_max_bound_default                -1
% 19.52/2.98  --bmc1_symbol_reachability              true
% 19.52/2.98  --bmc1_property_lemmas                  false
% 19.52/2.98  --bmc1_k_induction                      false
% 19.52/2.98  --bmc1_non_equiv_states                 false
% 19.52/2.98  --bmc1_deadlock                         false
% 19.52/2.98  --bmc1_ucm                              false
% 19.52/2.98  --bmc1_add_unsat_core                   none
% 19.52/2.98  --bmc1_unsat_core_children              false
% 19.52/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.52/2.98  --bmc1_out_stat                         full
% 19.52/2.98  --bmc1_ground_init                      false
% 19.52/2.98  --bmc1_pre_inst_next_state              false
% 19.52/2.98  --bmc1_pre_inst_state                   false
% 19.52/2.98  --bmc1_pre_inst_reach_state             false
% 19.52/2.98  --bmc1_out_unsat_core                   false
% 19.52/2.98  --bmc1_aig_witness_out                  false
% 19.52/2.98  --bmc1_verbose                          false
% 19.52/2.98  --bmc1_dump_clauses_tptp                false
% 19.52/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.52/2.98  --bmc1_dump_file                        -
% 19.52/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.52/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.52/2.98  --bmc1_ucm_extend_mode                  1
% 19.52/2.98  --bmc1_ucm_init_mode                    2
% 19.52/2.98  --bmc1_ucm_cone_mode                    none
% 19.52/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.52/2.98  --bmc1_ucm_relax_model                  4
% 19.52/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.52/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.52/2.98  --bmc1_ucm_layered_model                none
% 19.52/2.98  --bmc1_ucm_max_lemma_size               10
% 19.52/2.98  
% 19.52/2.98  ------ AIG Options
% 19.52/2.98  
% 19.52/2.98  --aig_mode                              false
% 19.52/2.98  
% 19.52/2.98  ------ Instantiation Options
% 19.52/2.98  
% 19.52/2.98  --instantiation_flag                    true
% 19.52/2.98  --inst_sos_flag                         true
% 19.52/2.98  --inst_sos_phase                        true
% 19.52/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.52/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.52/2.98  --inst_lit_sel_side                     num_symb
% 19.52/2.98  --inst_solver_per_active                1400
% 19.52/2.98  --inst_solver_calls_frac                1.
% 19.52/2.98  --inst_passive_queue_type               priority_queues
% 19.52/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.52/2.98  --inst_passive_queues_freq              [25;2]
% 19.52/2.98  --inst_dismatching                      true
% 19.52/2.98  --inst_eager_unprocessed_to_passive     true
% 19.52/2.98  --inst_prop_sim_given                   true
% 19.52/2.98  --inst_prop_sim_new                     false
% 19.52/2.98  --inst_subs_new                         false
% 19.52/2.98  --inst_eq_res_simp                      false
% 19.52/2.98  --inst_subs_given                       false
% 19.52/2.98  --inst_orphan_elimination               true
% 19.52/2.98  --inst_learning_loop_flag               true
% 19.52/2.98  --inst_learning_start                   3000
% 19.52/2.98  --inst_learning_factor                  2
% 19.52/2.98  --inst_start_prop_sim_after_learn       3
% 19.52/2.98  --inst_sel_renew                        solver
% 19.52/2.98  --inst_lit_activity_flag                true
% 19.52/2.98  --inst_restr_to_given                   false
% 19.52/2.98  --inst_activity_threshold               500
% 19.52/2.98  --inst_out_proof                        true
% 19.52/2.98  
% 19.52/2.98  ------ Resolution Options
% 19.52/2.98  
% 19.52/2.98  --resolution_flag                       true
% 19.52/2.98  --res_lit_sel                           adaptive
% 19.52/2.98  --res_lit_sel_side                      none
% 19.52/2.98  --res_ordering                          kbo
% 19.52/2.98  --res_to_prop_solver                    active
% 19.52/2.98  --res_prop_simpl_new                    false
% 19.52/2.98  --res_prop_simpl_given                  true
% 19.52/2.98  --res_passive_queue_type                priority_queues
% 19.52/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.52/2.98  --res_passive_queues_freq               [15;5]
% 19.52/2.98  --res_forward_subs                      full
% 19.52/2.98  --res_backward_subs                     full
% 19.52/2.98  --res_forward_subs_resolution           true
% 19.52/2.98  --res_backward_subs_resolution          true
% 19.52/2.98  --res_orphan_elimination                true
% 19.52/2.98  --res_time_limit                        2.
% 19.52/2.98  --res_out_proof                         true
% 19.52/2.98  
% 19.52/2.98  ------ Superposition Options
% 19.52/2.98  
% 19.52/2.98  --superposition_flag                    true
% 19.52/2.98  --sup_passive_queue_type                priority_queues
% 19.52/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.52/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.52/2.98  --demod_completeness_check              fast
% 19.52/2.98  --demod_use_ground                      true
% 19.52/2.98  --sup_to_prop_solver                    passive
% 19.52/2.98  --sup_prop_simpl_new                    true
% 19.52/2.98  --sup_prop_simpl_given                  true
% 19.52/2.98  --sup_fun_splitting                     true
% 19.52/2.98  --sup_smt_interval                      50000
% 19.52/2.98  
% 19.52/2.98  ------ Superposition Simplification Setup
% 19.52/2.98  
% 19.52/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.52/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.52/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.52/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.52/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.52/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.52/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.52/2.98  --sup_immed_triv                        [TrivRules]
% 19.52/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.52/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.52/2.98  --sup_immed_bw_main                     []
% 19.52/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.52/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.52/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.52/2.98  --sup_input_bw                          []
% 19.52/2.98  
% 19.52/2.98  ------ Combination Options
% 19.52/2.98  
% 19.52/2.98  --comb_res_mult                         3
% 19.52/2.98  --comb_sup_mult                         2
% 19.52/2.98  --comb_inst_mult                        10
% 19.52/2.98  
% 19.52/2.98  ------ Debug Options
% 19.52/2.98  
% 19.52/2.98  --dbg_backtrace                         false
% 19.52/2.98  --dbg_dump_prop_clauses                 false
% 19.52/2.98  --dbg_dump_prop_clauses_file            -
% 19.52/2.98  --dbg_out_stat                          false
% 19.52/2.98  ------ Parsing...
% 19.52/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.52/2.98  
% 19.52/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 19.52/2.98  
% 19.52/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.52/2.98  
% 19.52/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.52/2.98  ------ Proving...
% 19.52/2.98  ------ Problem Properties 
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  clauses                                 30
% 19.52/2.98  conjectures                             4
% 19.52/2.98  EPR                                     2
% 19.52/2.98  Horn                                    14
% 19.52/2.98  unary                                   4
% 19.52/2.98  binary                                  10
% 19.52/2.98  lits                                    83
% 19.52/2.98  lits eq                                 18
% 19.52/2.98  fd_pure                                 0
% 19.52/2.98  fd_pseudo                               0
% 19.52/2.98  fd_cond                                 5
% 19.52/2.98  fd_pseudo_cond                          4
% 19.52/2.98  AC symbols                              0
% 19.52/2.98  
% 19.52/2.98  ------ Schedule dynamic 5 is on 
% 19.52/2.98  
% 19.52/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  ------ 
% 19.52/2.98  Current options:
% 19.52/2.98  ------ 
% 19.52/2.98  
% 19.52/2.98  ------ Input Options
% 19.52/2.98  
% 19.52/2.98  --out_options                           all
% 19.52/2.98  --tptp_safe_out                         true
% 19.52/2.98  --problem_path                          ""
% 19.52/2.98  --include_path                          ""
% 19.52/2.98  --clausifier                            res/vclausify_rel
% 19.52/2.98  --clausifier_options                    ""
% 19.52/2.98  --stdin                                 false
% 19.52/2.98  --stats_out                             all
% 19.52/2.98  
% 19.52/2.98  ------ General Options
% 19.52/2.98  
% 19.52/2.98  --fof                                   false
% 19.52/2.98  --time_out_real                         305.
% 19.52/2.98  --time_out_virtual                      -1.
% 19.52/2.98  --symbol_type_check                     false
% 19.52/2.98  --clausify_out                          false
% 19.52/2.98  --sig_cnt_out                           false
% 19.52/2.98  --trig_cnt_out                          false
% 19.52/2.98  --trig_cnt_out_tolerance                1.
% 19.52/2.98  --trig_cnt_out_sk_spl                   false
% 19.52/2.98  --abstr_cl_out                          false
% 19.52/2.98  
% 19.52/2.98  ------ Global Options
% 19.52/2.98  
% 19.52/2.98  --schedule                              default
% 19.52/2.98  --add_important_lit                     false
% 19.52/2.98  --prop_solver_per_cl                    1000
% 19.52/2.98  --min_unsat_core                        false
% 19.52/2.98  --soft_assumptions                      false
% 19.52/2.98  --soft_lemma_size                       3
% 19.52/2.98  --prop_impl_unit_size                   0
% 19.52/2.98  --prop_impl_unit                        []
% 19.52/2.98  --share_sel_clauses                     true
% 19.52/2.98  --reset_solvers                         false
% 19.52/2.98  --bc_imp_inh                            [conj_cone]
% 19.52/2.98  --conj_cone_tolerance                   3.
% 19.52/2.98  --extra_neg_conj                        none
% 19.52/2.98  --large_theory_mode                     true
% 19.52/2.98  --prolific_symb_bound                   200
% 19.52/2.98  --lt_threshold                          2000
% 19.52/2.98  --clause_weak_htbl                      true
% 19.52/2.98  --gc_record_bc_elim                     false
% 19.52/2.98  
% 19.52/2.98  ------ Preprocessing Options
% 19.52/2.98  
% 19.52/2.98  --preprocessing_flag                    true
% 19.52/2.98  --time_out_prep_mult                    0.1
% 19.52/2.98  --splitting_mode                        input
% 19.52/2.98  --splitting_grd                         true
% 19.52/2.98  --splitting_cvd                         false
% 19.52/2.98  --splitting_cvd_svl                     false
% 19.52/2.98  --splitting_nvd                         32
% 19.52/2.98  --sub_typing                            true
% 19.52/2.98  --prep_gs_sim                           true
% 19.52/2.98  --prep_unflatten                        true
% 19.52/2.98  --prep_res_sim                          true
% 19.52/2.98  --prep_upred                            true
% 19.52/2.98  --prep_sem_filter                       exhaustive
% 19.52/2.98  --prep_sem_filter_out                   false
% 19.52/2.98  --pred_elim                             true
% 19.52/2.98  --res_sim_input                         true
% 19.52/2.98  --eq_ax_congr_red                       true
% 19.52/2.98  --pure_diseq_elim                       true
% 19.52/2.98  --brand_transform                       false
% 19.52/2.98  --non_eq_to_eq                          false
% 19.52/2.98  --prep_def_merge                        true
% 19.52/2.98  --prep_def_merge_prop_impl              false
% 19.52/2.98  --prep_def_merge_mbd                    true
% 19.52/2.98  --prep_def_merge_tr_red                 false
% 19.52/2.98  --prep_def_merge_tr_cl                  false
% 19.52/2.98  --smt_preprocessing                     true
% 19.52/2.98  --smt_ac_axioms                         fast
% 19.52/2.98  --preprocessed_out                      false
% 19.52/2.98  --preprocessed_stats                    false
% 19.52/2.98  
% 19.52/2.98  ------ Abstraction refinement Options
% 19.52/2.98  
% 19.52/2.98  --abstr_ref                             []
% 19.52/2.98  --abstr_ref_prep                        false
% 19.52/2.98  --abstr_ref_until_sat                   false
% 19.52/2.98  --abstr_ref_sig_restrict                funpre
% 19.52/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.52/2.98  --abstr_ref_under                       []
% 19.52/2.98  
% 19.52/2.98  ------ SAT Options
% 19.52/2.98  
% 19.52/2.98  --sat_mode                              false
% 19.52/2.98  --sat_fm_restart_options                ""
% 19.52/2.98  --sat_gr_def                            false
% 19.52/2.98  --sat_epr_types                         true
% 19.52/2.98  --sat_non_cyclic_types                  false
% 19.52/2.98  --sat_finite_models                     false
% 19.52/2.98  --sat_fm_lemmas                         false
% 19.52/2.98  --sat_fm_prep                           false
% 19.52/2.98  --sat_fm_uc_incr                        true
% 19.52/2.98  --sat_out_model                         small
% 19.52/2.98  --sat_out_clauses                       false
% 19.52/2.98  
% 19.52/2.98  ------ QBF Options
% 19.52/2.98  
% 19.52/2.98  --qbf_mode                              false
% 19.52/2.98  --qbf_elim_univ                         false
% 19.52/2.98  --qbf_dom_inst                          none
% 19.52/2.98  --qbf_dom_pre_inst                      false
% 19.52/2.98  --qbf_sk_in                             false
% 19.52/2.98  --qbf_pred_elim                         true
% 19.52/2.98  --qbf_split                             512
% 19.52/2.98  
% 19.52/2.98  ------ BMC1 Options
% 19.52/2.98  
% 19.52/2.98  --bmc1_incremental                      false
% 19.52/2.98  --bmc1_axioms                           reachable_all
% 19.52/2.98  --bmc1_min_bound                        0
% 19.52/2.98  --bmc1_max_bound                        -1
% 19.52/2.98  --bmc1_max_bound_default                -1
% 19.52/2.98  --bmc1_symbol_reachability              true
% 19.52/2.98  --bmc1_property_lemmas                  false
% 19.52/2.98  --bmc1_k_induction                      false
% 19.52/2.98  --bmc1_non_equiv_states                 false
% 19.52/2.98  --bmc1_deadlock                         false
% 19.52/2.98  --bmc1_ucm                              false
% 19.52/2.98  --bmc1_add_unsat_core                   none
% 19.52/2.98  --bmc1_unsat_core_children              false
% 19.52/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.52/2.98  --bmc1_out_stat                         full
% 19.52/2.98  --bmc1_ground_init                      false
% 19.52/2.98  --bmc1_pre_inst_next_state              false
% 19.52/2.98  --bmc1_pre_inst_state                   false
% 19.52/2.98  --bmc1_pre_inst_reach_state             false
% 19.52/2.98  --bmc1_out_unsat_core                   false
% 19.52/2.98  --bmc1_aig_witness_out                  false
% 19.52/2.98  --bmc1_verbose                          false
% 19.52/2.98  --bmc1_dump_clauses_tptp                false
% 19.52/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.52/2.98  --bmc1_dump_file                        -
% 19.52/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.52/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.52/2.98  --bmc1_ucm_extend_mode                  1
% 19.52/2.98  --bmc1_ucm_init_mode                    2
% 19.52/2.98  --bmc1_ucm_cone_mode                    none
% 19.52/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.52/2.98  --bmc1_ucm_relax_model                  4
% 19.52/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.52/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.52/2.98  --bmc1_ucm_layered_model                none
% 19.52/2.98  --bmc1_ucm_max_lemma_size               10
% 19.52/2.98  
% 19.52/2.98  ------ AIG Options
% 19.52/2.98  
% 19.52/2.98  --aig_mode                              false
% 19.52/2.98  
% 19.52/2.98  ------ Instantiation Options
% 19.52/2.98  
% 19.52/2.98  --instantiation_flag                    true
% 19.52/2.98  --inst_sos_flag                         true
% 19.52/2.98  --inst_sos_phase                        true
% 19.52/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.52/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.52/2.98  --inst_lit_sel_side                     none
% 19.52/2.98  --inst_solver_per_active                1400
% 19.52/2.98  --inst_solver_calls_frac                1.
% 19.52/2.98  --inst_passive_queue_type               priority_queues
% 19.52/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.52/2.98  --inst_passive_queues_freq              [25;2]
% 19.52/2.98  --inst_dismatching                      true
% 19.52/2.98  --inst_eager_unprocessed_to_passive     true
% 19.52/2.98  --inst_prop_sim_given                   true
% 19.52/2.98  --inst_prop_sim_new                     false
% 19.52/2.98  --inst_subs_new                         false
% 19.52/2.98  --inst_eq_res_simp                      false
% 19.52/2.98  --inst_subs_given                       false
% 19.52/2.98  --inst_orphan_elimination               true
% 19.52/2.98  --inst_learning_loop_flag               true
% 19.52/2.98  --inst_learning_start                   3000
% 19.52/2.98  --inst_learning_factor                  2
% 19.52/2.98  --inst_start_prop_sim_after_learn       3
% 19.52/2.98  --inst_sel_renew                        solver
% 19.52/2.98  --inst_lit_activity_flag                true
% 19.52/2.98  --inst_restr_to_given                   false
% 19.52/2.98  --inst_activity_threshold               500
% 19.52/2.98  --inst_out_proof                        true
% 19.52/2.98  
% 19.52/2.98  ------ Resolution Options
% 19.52/2.98  
% 19.52/2.98  --resolution_flag                       false
% 19.52/2.98  --res_lit_sel                           adaptive
% 19.52/2.98  --res_lit_sel_side                      none
% 19.52/2.98  --res_ordering                          kbo
% 19.52/2.98  --res_to_prop_solver                    active
% 19.52/2.98  --res_prop_simpl_new                    false
% 19.52/2.98  --res_prop_simpl_given                  true
% 19.52/2.98  --res_passive_queue_type                priority_queues
% 19.52/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.52/2.98  --res_passive_queues_freq               [15;5]
% 19.52/2.98  --res_forward_subs                      full
% 19.52/2.98  --res_backward_subs                     full
% 19.52/2.98  --res_forward_subs_resolution           true
% 19.52/2.98  --res_backward_subs_resolution          true
% 19.52/2.98  --res_orphan_elimination                true
% 19.52/2.98  --res_time_limit                        2.
% 19.52/2.98  --res_out_proof                         true
% 19.52/2.98  
% 19.52/2.98  ------ Superposition Options
% 19.52/2.98  
% 19.52/2.98  --superposition_flag                    true
% 19.52/2.98  --sup_passive_queue_type                priority_queues
% 19.52/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.52/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.52/2.98  --demod_completeness_check              fast
% 19.52/2.98  --demod_use_ground                      true
% 19.52/2.98  --sup_to_prop_solver                    passive
% 19.52/2.98  --sup_prop_simpl_new                    true
% 19.52/2.98  --sup_prop_simpl_given                  true
% 19.52/2.98  --sup_fun_splitting                     true
% 19.52/2.98  --sup_smt_interval                      50000
% 19.52/2.98  
% 19.52/2.98  ------ Superposition Simplification Setup
% 19.52/2.98  
% 19.52/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.52/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.52/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.52/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.52/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.52/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.52/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.52/2.98  --sup_immed_triv                        [TrivRules]
% 19.52/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.52/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.52/2.98  --sup_immed_bw_main                     []
% 19.52/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.52/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.52/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.52/2.98  --sup_input_bw                          []
% 19.52/2.98  
% 19.52/2.98  ------ Combination Options
% 19.52/2.98  
% 19.52/2.98  --comb_res_mult                         3
% 19.52/2.98  --comb_sup_mult                         2
% 19.52/2.98  --comb_inst_mult                        10
% 19.52/2.98  
% 19.52/2.98  ------ Debug Options
% 19.52/2.98  
% 19.52/2.98  --dbg_backtrace                         false
% 19.52/2.98  --dbg_dump_prop_clauses                 false
% 19.52/2.98  --dbg_dump_prop_clauses_file            -
% 19.52/2.98  --dbg_out_stat                          false
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  ------ Proving...
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  % SZS status Theorem for theBenchmark.p
% 19.52/2.98  
% 19.52/2.98   Resolution empty clause
% 19.52/2.98  
% 19.52/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.52/2.98  
% 19.52/2.98  fof(f4,axiom,(
% 19.52/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f18,plain,(
% 19.52/2.98    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(ennf_transformation,[],[f4])).
% 19.52/2.98  
% 19.52/2.98  fof(f33,plain,(
% 19.52/2.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(nnf_transformation,[],[f18])).
% 19.52/2.98  
% 19.52/2.98  fof(f34,plain,(
% 19.52/2.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(flattening,[],[f33])).
% 19.52/2.98  
% 19.52/2.98  fof(f35,plain,(
% 19.52/2.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(rectify,[],[f34])).
% 19.52/2.98  
% 19.52/2.98  fof(f36,plain,(
% 19.52/2.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f37,plain,(
% 19.52/2.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 19.52/2.98  
% 19.52/2.98  fof(f71,plain,(
% 19.52/2.98    ( ! [X2,X0,X1] : (k1_wellord1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f37])).
% 19.52/2.98  
% 19.52/2.98  fof(f11,conjecture,(
% 19.52/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f12,negated_conjecture,(
% 19.52/2.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 19.52/2.98    inference(negated_conjecture,[],[f11])).
% 19.52/2.98  
% 19.52/2.98  fof(f27,plain,(
% 19.52/2.98    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 19.52/2.98    inference(ennf_transformation,[],[f12])).
% 19.52/2.98  
% 19.52/2.98  fof(f28,plain,(
% 19.52/2.98    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 19.52/2.98    inference(flattening,[],[f27])).
% 19.52/2.98  
% 19.52/2.98  fof(f57,plain,(
% 19.52/2.98    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 19.52/2.98    inference(nnf_transformation,[],[f28])).
% 19.52/2.98  
% 19.52/2.98  fof(f58,plain,(
% 19.52/2.98    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 19.52/2.98    inference(flattening,[],[f57])).
% 19.52/2.98  
% 19.52/2.98  fof(f59,plain,(
% 19.52/2.98    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) | ~r2_hidden(k4_tarski(sK9,sK10),sK11)) & (r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) | r2_hidden(k4_tarski(sK9,sK10),sK11)) & r2_hidden(sK10,k3_relat_1(sK11)) & r2_hidden(sK9,k3_relat_1(sK11)) & v2_wellord1(sK11) & v1_relat_1(sK11))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f60,plain,(
% 19.52/2.98    (~r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) | ~r2_hidden(k4_tarski(sK9,sK10),sK11)) & (r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) | r2_hidden(k4_tarski(sK9,sK10),sK11)) & r2_hidden(sK10,k3_relat_1(sK11)) & r2_hidden(sK9,k3_relat_1(sK11)) & v2_wellord1(sK11) & v1_relat_1(sK11)),
% 19.52/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f58,f59])).
% 19.52/2.98  
% 19.52/2.98  fof(f99,plain,(
% 19.52/2.98    v1_relat_1(sK11)),
% 19.52/2.98    inference(cnf_transformation,[],[f60])).
% 19.52/2.98  
% 19.52/2.98  fof(f2,axiom,(
% 19.52/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f15,plain,(
% 19.52/2.98    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 19.52/2.98    inference(ennf_transformation,[],[f2])).
% 19.52/2.98  
% 19.52/2.98  fof(f16,plain,(
% 19.52/2.98    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 19.52/2.98    inference(flattening,[],[f15])).
% 19.52/2.98  
% 19.52/2.98  fof(f65,plain,(
% 19.52/2.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f16])).
% 19.52/2.98  
% 19.52/2.98  fof(f68,plain,(
% 19.52/2.98    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f37])).
% 19.52/2.98  
% 19.52/2.98  fof(f106,plain,(
% 19.52/2.98    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(equality_resolution,[],[f68])).
% 19.52/2.98  
% 19.52/2.98  fof(f1,axiom,(
% 19.52/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f14,plain,(
% 19.52/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.52/2.98    inference(ennf_transformation,[],[f1])).
% 19.52/2.98  
% 19.52/2.98  fof(f29,plain,(
% 19.52/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.52/2.98    inference(nnf_transformation,[],[f14])).
% 19.52/2.98  
% 19.52/2.98  fof(f30,plain,(
% 19.52/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.52/2.98    inference(rectify,[],[f29])).
% 19.52/2.98  
% 19.52/2.98  fof(f31,plain,(
% 19.52/2.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f32,plain,(
% 19.52/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.52/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 19.52/2.98  
% 19.52/2.98  fof(f61,plain,(
% 19.52/2.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f32])).
% 19.52/2.98  
% 19.52/2.98  fof(f3,axiom,(
% 19.52/2.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f17,plain,(
% 19.52/2.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 19.52/2.98    inference(ennf_transformation,[],[f3])).
% 19.52/2.98  
% 19.52/2.98  fof(f66,plain,(
% 19.52/2.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f17])).
% 19.52/2.98  
% 19.52/2.98  fof(f9,axiom,(
% 19.52/2.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f24,plain,(
% 19.52/2.98    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.52/2.98    inference(ennf_transformation,[],[f9])).
% 19.52/2.98  
% 19.52/2.98  fof(f90,plain,(
% 19.52/2.98    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f24])).
% 19.52/2.98  
% 19.52/2.98  fof(f62,plain,(
% 19.52/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f32])).
% 19.52/2.98  
% 19.52/2.98  fof(f8,axiom,(
% 19.52/2.98    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f22,plain,(
% 19.52/2.98    ! [X0] : ((! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(ennf_transformation,[],[f8])).
% 19.52/2.98  
% 19.52/2.98  fof(f23,plain,(
% 19.52/2.98    ! [X0] : (! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(flattening,[],[f22])).
% 19.52/2.98  
% 19.52/2.98  fof(f48,plain,(
% 19.52/2.98    ! [X1,X0] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X0,X1),X1)))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f49,plain,(
% 19.52/2.98    ! [X0] : (! [X1] : ((! [X3] : (r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X0,X1),X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f48])).
% 19.52/2.98  
% 19.52/2.98  fof(f88,plain,(
% 19.52/2.98    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f49])).
% 19.52/2.98  
% 19.52/2.98  fof(f100,plain,(
% 19.52/2.98    v2_wellord1(sK11)),
% 19.52/2.98    inference(cnf_transformation,[],[f60])).
% 19.52/2.98  
% 19.52/2.98  fof(f7,axiom,(
% 19.52/2.98    ! [X0,X1] : (v1_relat_1(X0) => ? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f21,plain,(
% 19.52/2.98    ! [X0,X1] : (? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(ennf_transformation,[],[f7])).
% 19.52/2.98  
% 19.52/2.98  fof(f44,plain,(
% 19.52/2.98    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(nnf_transformation,[],[f21])).
% 19.52/2.98  
% 19.52/2.98  fof(f45,plain,(
% 19.52/2.98    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(flattening,[],[f44])).
% 19.52/2.98  
% 19.52/2.98  fof(f46,plain,(
% 19.52/2.98    ! [X1,X0] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) => ! [X3] : ((r2_hidden(X3,sK4(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK4(X0,X1)))))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f47,plain,(
% 19.52/2.98    ! [X0,X1] : (! [X3] : ((r2_hidden(X3,sK4(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK4(X0,X1)))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 19.52/2.98  
% 19.52/2.98  fof(f87,plain,(
% 19.52/2.98    ( ! [X0,X3,X1] : (r2_hidden(X3,sK4(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f47])).
% 19.52/2.98  
% 19.52/2.98  fof(f63,plain,(
% 19.52/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f32])).
% 19.52/2.98  
% 19.52/2.98  fof(f6,axiom,(
% 19.52/2.98    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f20,plain,(
% 19.52/2.98    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(ennf_transformation,[],[f6])).
% 19.52/2.98  
% 19.52/2.98  fof(f40,plain,(
% 19.52/2.98    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(nnf_transformation,[],[f20])).
% 19.52/2.98  
% 19.52/2.98  fof(f41,plain,(
% 19.52/2.98    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(rectify,[],[f40])).
% 19.52/2.98  
% 19.52/2.98  fof(f42,plain,(
% 19.52/2.98    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) & ~r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & sK2(X0) != sK3(X0) & r2_hidden(sK3(X0),k3_relat_1(X0)) & r2_hidden(sK2(X0),k3_relat_1(X0))))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f43,plain,(
% 19.52/2.98    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) & ~r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & sK2(X0) != sK3(X0) & r2_hidden(sK3(X0),k3_relat_1(X0)) & r2_hidden(sK2(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).
% 19.52/2.98  
% 19.52/2.98  fof(f79,plain,(
% 19.52/2.98    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f43])).
% 19.52/2.98  
% 19.52/2.98  fof(f5,axiom,(
% 19.52/2.98    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f19,plain,(
% 19.52/2.98    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(ennf_transformation,[],[f5])).
% 19.52/2.98  
% 19.52/2.98  fof(f38,plain,(
% 19.52/2.98    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(nnf_transformation,[],[f19])).
% 19.52/2.98  
% 19.52/2.98  fof(f39,plain,(
% 19.52/2.98    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 19.52/2.98    inference(flattening,[],[f38])).
% 19.52/2.98  
% 19.52/2.98  fof(f76,plain,(
% 19.52/2.98    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f39])).
% 19.52/2.98  
% 19.52/2.98  fof(f69,plain,(
% 19.52/2.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f37])).
% 19.52/2.98  
% 19.52/2.98  fof(f105,plain,(
% 19.52/2.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(equality_resolution,[],[f69])).
% 19.52/2.98  
% 19.52/2.98  fof(f10,axiom,(
% 19.52/2.98    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 19.52/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.52/2.98  
% 19.52/2.98  fof(f13,plain,(
% 19.52/2.98    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 19.52/2.98    inference(rectify,[],[f10])).
% 19.52/2.98  
% 19.52/2.98  fof(f25,plain,(
% 19.52/2.98    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 19.52/2.98    inference(ennf_transformation,[],[f13])).
% 19.52/2.98  
% 19.52/2.98  fof(f26,plain,(
% 19.52/2.98    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.52/2.98    inference(flattening,[],[f25])).
% 19.52/2.98  
% 19.52/2.98  fof(f50,plain,(
% 19.52/2.98    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.52/2.98    inference(nnf_transformation,[],[f26])).
% 19.52/2.98  
% 19.52/2.98  fof(f51,plain,(
% 19.52/2.98    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.52/2.98    inference(flattening,[],[f50])).
% 19.52/2.98  
% 19.52/2.98  fof(f52,plain,(
% 19.52/2.98    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.52/2.98    inference(rectify,[],[f51])).
% 19.52/2.98  
% 19.52/2.98  fof(f55,plain,(
% 19.52/2.98    ( ! [X3] : (! [X1,X0] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) => (~r2_hidden(sK8(X0,X1),X0) & r2_hidden(k4_tarski(sK8(X0,X1),X3),X1)))) )),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f54,plain,(
% 19.52/2.98    ! [X1,X0] : (? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0)) => (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,sK7(X0,X1)),X1)) & r2_hidden(sK7(X0,X1),X0)))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f53,plain,(
% 19.52/2.98    ! [X1,X0] : (? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) => (k1_wellord1(X1,sK6(X0,X1)) = X0 & r2_hidden(sK6(X0,X1),k3_relat_1(X1))))),
% 19.52/2.98    introduced(choice_axiom,[])).
% 19.52/2.98  
% 19.52/2.98  fof(f56,plain,(
% 19.52/2.98    ! [X0,X1] : ((((k1_wellord1(X1,sK6(X0,X1)) = X0 & r2_hidden(sK6(X0,X1),k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ((~r2_hidden(sK8(X0,X1),X0) & r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X1)) & r2_hidden(sK7(X0,X1),X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.52/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f55,f54,f53])).
% 19.52/2.98  
% 19.52/2.98  fof(f92,plain,(
% 19.52/2.98    ( ! [X6,X0,X7,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,X0) | k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f56])).
% 19.52/2.98  
% 19.52/2.98  fof(f109,plain,(
% 19.52/2.98    ( ! [X6,X7,X5,X1] : (r2_hidden(X6,k1_wellord1(X1,X7)) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,k1_wellord1(X1,X7)) | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 19.52/2.98    inference(equality_resolution,[],[f92])).
% 19.52/2.98  
% 19.52/2.98  fof(f64,plain,(
% 19.52/2.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f16])).
% 19.52/2.98  
% 19.52/2.98  fof(f104,plain,(
% 19.52/2.98    ~r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) | ~r2_hidden(k4_tarski(sK9,sK10),sK11)),
% 19.52/2.98    inference(cnf_transformation,[],[f60])).
% 19.52/2.98  
% 19.52/2.98  fof(f101,plain,(
% 19.52/2.98    r2_hidden(sK9,k3_relat_1(sK11))),
% 19.52/2.98    inference(cnf_transformation,[],[f60])).
% 19.52/2.98  
% 19.52/2.98  fof(f102,plain,(
% 19.52/2.98    r2_hidden(sK10,k3_relat_1(sK11))),
% 19.52/2.98    inference(cnf_transformation,[],[f60])).
% 19.52/2.98  
% 19.52/2.98  fof(f67,plain,(
% 19.52/2.98    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f37])).
% 19.52/2.98  
% 19.52/2.98  fof(f107,plain,(
% 19.52/2.98    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(equality_resolution,[],[f67])).
% 19.52/2.98  
% 19.52/2.98  fof(f108,plain,(
% 19.52/2.98    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(equality_resolution,[],[f107])).
% 19.52/2.98  
% 19.52/2.98  fof(f103,plain,(
% 19.52/2.98    r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) | r2_hidden(k4_tarski(sK9,sK10),sK11)),
% 19.52/2.98    inference(cnf_transformation,[],[f60])).
% 19.52/2.98  
% 19.52/2.98  fof(f89,plain,(
% 19.52/2.98    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f49])).
% 19.52/2.98  
% 19.52/2.98  fof(f86,plain,(
% 19.52/2.98    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,sK4(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f47])).
% 19.52/2.98  
% 19.52/2.98  fof(f85,plain,(
% 19.52/2.98    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(X3,sK4(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.52/2.98    inference(cnf_transformation,[],[f47])).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7,plain,
% 19.52/2.98      ( r2_hidden(sK1(X0,X1,X2),X2)
% 19.52/2.98      | r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
% 19.52/2.98      | ~ v1_relat_1(X0)
% 19.52/2.98      | k1_wellord1(X0,X1) = X2 ),
% 19.52/2.98      inference(cnf_transformation,[],[f71]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_43,negated_conjecture,
% 19.52/2.98      ( v1_relat_1(sK11) ),
% 19.52/2.98      inference(cnf_transformation,[],[f99]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_991,plain,
% 19.52/2.98      ( r2_hidden(sK1(X0,X1,X2),X2)
% 19.52/2.98      | r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
% 19.52/2.98      | k1_wellord1(X0,X1) = X2
% 19.52/2.98      | sK11 != X0 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_7,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_992,plain,
% 19.52/2.98      ( r2_hidden(sK1(sK11,X0,X1),X1)
% 19.52/2.98      | r2_hidden(k4_tarski(sK1(sK11,X0,X1),X0),sK11)
% 19.52/2.98      | k1_wellord1(sK11,X0) = X1 ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_991]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3482,plain,
% 19.52/2.98      ( k1_wellord1(sK11,X0) = X1
% 19.52/2.98      | r2_hidden(sK1(sK11,X0,X1),X1) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(sK1(sK11,X0,X1),X0),sK11) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 19.52/2.98      | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f65]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_947,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_3,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_948,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) | ~ r2_hidden(k4_tarski(X1,X0),sK11) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_947]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3485,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X1,X0),sK11) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5594,plain,
% 19.52/2.98      ( k1_wellord1(sK11,X0) = X1
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r2_hidden(sK1(sK11,X0,X1),X1) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3482,c_3485]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_10,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f106]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_910,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_10,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_911,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_910]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3488,plain,
% 19.52/2.98      ( r2_hidden(X0,k1_wellord1(sK11,X1)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_8118,plain,
% 19.52/2.98      ( k1_wellord1(sK11,X0) = k1_wellord1(sK11,X1)
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(sK1(sK11,X0,k1_wellord1(sK11,X1)),X1),sK11) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_5594,c_3488]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_2,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.52/2.98      inference(cnf_transformation,[],[f61]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3507,plain,
% 19.52/2.98      ( r2_hidden(X0,X1) != iProver_top
% 19.52/2.98      | r2_hidden(X0,X2) = iProver_top
% 19.52/2.98      | r1_tarski(X1,X2) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_13282,plain,
% 19.52/2.98      ( k1_wellord1(sK11,X0) = k1_wellord1(sK11,X1)
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(sK1(sK11,X0,k1_wellord1(sK11,X1)),X1),X2) = iProver_top
% 19.52/2.98      | r1_tarski(sK11,X2) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_8118,c_3507]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 19.52/2.98      inference(cnf_transformation,[],[f66]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3506,plain,
% 19.52/2.98      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_62876,plain,
% 19.52/2.98      ( k1_wellord1(sK11,X0) = k1_wellord1(sK11,X1)
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r1_tarski(X2,k4_tarski(sK1(sK11,X0,k1_wellord1(sK11,X1)),X1)) != iProver_top
% 19.52/2.98      | r1_tarski(sK11,X2) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_13282,c_3506]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_29,plain,
% 19.52/2.98      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 19.52/2.98      inference(cnf_transformation,[],[f90]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_957,plain,
% 19.52/2.98      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) | sK11 != X0 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_29,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_958,plain,
% 19.52/2.98      ( r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_957]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_959,plain,
% 19.52/2.98      ( r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3713,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) | ~ r2_hidden(k4_tarski(sK9,X0),sK11) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_948]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3714,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(sK9,X0),sK11) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_3713]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_2847,plain,( X0 = X0 ),theory(equality) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4510,plain,
% 19.52/2.98      ( sK9 = sK9 ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_2847]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5284,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,X0),sK11)
% 19.52/2.98      | ~ r2_hidden(sK9,k1_wellord1(sK11,X0)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_911]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5285,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,X0),sK11) = iProver_top
% 19.52/2.98      | r2_hidden(sK9,k1_wellord1(sK11,X0)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_5284]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_1,plain,
% 19.52/2.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f62]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3508,plain,
% 19.52/2.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.52/2.98      | r1_tarski(X0,X1) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4851,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X0),sK11) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3508,c_3488]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5946,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_4851,c_3485]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_28,plain,
% 19.52/2.98      ( r2_hidden(sK5(X0,X1),X1)
% 19.52/2.98      | ~ r1_tarski(X1,k3_relat_1(X0))
% 19.52/2.98      | ~ v2_wellord1(X0)
% 19.52/2.98      | ~ v1_relat_1(X0)
% 19.52/2.98      | k1_xboole_0 = X1 ),
% 19.52/2.98      inference(cnf_transformation,[],[f88]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_42,negated_conjecture,
% 19.52/2.98      ( v2_wellord1(sK11) ),
% 19.52/2.98      inference(cnf_transformation,[],[f100]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_565,plain,
% 19.52/2.98      ( r2_hidden(sK5(X0,X1),X1)
% 19.52/2.98      | ~ r1_tarski(X1,k3_relat_1(X0))
% 19.52/2.98      | ~ v1_relat_1(X0)
% 19.52/2.98      | sK11 != X0
% 19.52/2.98      | k1_xboole_0 = X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_28,c_42]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_566,plain,
% 19.52/2.98      ( r2_hidden(sK5(sK11,X0),X0)
% 19.52/2.98      | ~ r1_tarski(X0,k3_relat_1(sK11))
% 19.52/2.98      | ~ v1_relat_1(sK11)
% 19.52/2.98      | k1_xboole_0 = X0 ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_565]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_570,plain,
% 19.52/2.98      ( ~ r1_tarski(X0,k3_relat_1(sK11))
% 19.52/2.98      | r2_hidden(sK5(sK11,X0),X0)
% 19.52/2.98      | k1_xboole_0 = X0 ),
% 19.52/2.98      inference(global_propositional_subsumption,[status(thm)],[c_566,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_571,plain,
% 19.52/2.98      ( r2_hidden(sK5(sK11,X0),X0)
% 19.52/2.98      | ~ r1_tarski(X0,k3_relat_1(sK11))
% 19.52/2.98      | k1_xboole_0 = X0 ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_570]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3501,plain,
% 19.52/2.98      ( k1_xboole_0 = X0
% 19.52/2.98      | r2_hidden(sK5(sK11,X0),X0) = iProver_top
% 19.52/2.98      | r1_tarski(X0,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5405,plain,
% 19.52/2.98      ( k1_xboole_0 = X0
% 19.52/2.98      | r1_tarski(X0,sK5(sK11,X0)) != iProver_top
% 19.52/2.98      | r1_tarski(X0,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3501,c_3506]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_8067,plain,
% 19.52/2.98      ( k1_wellord1(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_5946,c_5405]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_2850,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.52/2.98      theory(equality) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3623,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1)
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X3))
% 19.52/2.98      | X2 != X0
% 19.52/2.98      | k1_wellord1(sK11,X3) != X1 ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_2850]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_11971,plain,
% 19.52/2.98      ( r2_hidden(X0,k1_wellord1(sK11,X1))
% 19.52/2.98      | ~ r2_hidden(sK9,k1_xboole_0)
% 19.52/2.98      | X0 != sK9
% 19.52/2.98      | k1_wellord1(sK11,X1) != k1_xboole_0 ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_3623]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_39312,plain,
% 19.52/2.98      ( r2_hidden(sK9,k1_wellord1(sK11,X0))
% 19.52/2.98      | ~ r2_hidden(sK9,k1_xboole_0)
% 19.52/2.98      | k1_wellord1(sK11,X0) != k1_xboole_0
% 19.52/2.98      | sK9 != sK9 ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_11971]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_39313,plain,
% 19.52/2.98      ( k1_wellord1(sK11,X0) != k1_xboole_0
% 19.52/2.98      | sK9 != sK9
% 19.52/2.98      | r2_hidden(sK9,k1_wellord1(sK11,X0)) = iProver_top
% 19.52/2.98      | r2_hidden(sK9,k1_xboole_0) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_39312]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_24,plain,
% 19.52/2.98      ( r2_hidden(X0,sK4(X1,X2))
% 19.52/2.98      | ~ r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f87]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_859,plain,
% 19.52/2.98      ( r2_hidden(X0,sK4(X1,X2))
% 19.52/2.98      | ~ r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_24,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_860,plain,
% 19.52/2.98      ( r2_hidden(X0,sK4(sK11,X1))
% 19.52/2.98      | ~ r2_hidden(X0,k3_relat_1(sK11))
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_859]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3491,plain,
% 19.52/2.98      ( r2_hidden(X0,sK4(sK11,X1)) = iProver_top
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_0,plain,
% 19.52/2.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f63]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3509,plain,
% 19.52/2.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 19.52/2.98      | r1_tarski(X0,X1) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4166,plain,
% 19.52/2.98      ( r1_tarski(X0,X0) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3508,c_3509]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_23,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(X2,k3_relat_1(X1))
% 19.52/2.98      | r2_hidden(k4_tarski(X2,X0),X1)
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | ~ v6_relat_2(X1)
% 19.52/2.98      | ~ v1_relat_1(X1)
% 19.52/2.98      | X0 = X2 ),
% 19.52/2.98      inference(cnf_transformation,[],[f79]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_874,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(X2,k3_relat_1(X1))
% 19.52/2.98      | r2_hidden(k4_tarski(X2,X0),X1)
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | ~ v6_relat_2(X1)
% 19.52/2.98      | X2 = X0
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_23,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_875,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11)
% 19.52/2.98      | r2_hidden(k4_tarski(X1,X0),sK11)
% 19.52/2.98      | ~ v6_relat_2(sK11)
% 19.52/2.98      | X0 = X1 ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_874]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_14,plain,
% 19.52/2.98      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 19.52/2.98      inference(cnf_transformation,[],[f76]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_116,plain,
% 19.52/2.98      ( v6_relat_2(sK11) | ~ v2_wellord1(sK11) | ~ v1_relat_1(sK11) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_14]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_879,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(X1,X0),sK11)
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11)
% 19.52/2.98      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(X0,k3_relat_1(sK11))
% 19.52/2.98      | X0 = X1 ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_875,c_43,c_42,c_116]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_880,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 19.52/2.98      | r2_hidden(k4_tarski(X1,X0),sK11)
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11)
% 19.52/2.98      | X1 = X0 ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_879]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3490,plain,
% 19.52/2.98      ( X0 = X1
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_880]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_9,plain,
% 19.52/2.98      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | ~ v1_relat_1(X1)
% 19.52/2.98      | X0 = X2 ),
% 19.52/2.98      inference(cnf_transformation,[],[f105]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_920,plain,
% 19.52/2.98      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | X2 = X0
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_9,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_921,plain,
% 19.52/2.98      ( r2_hidden(X0,k1_wellord1(sK11,X1))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 19.52/2.98      | X1 = X0 ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_920]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3487,plain,
% 19.52/2.98      ( X0 = X1
% 19.52/2.98      | r2_hidden(X1,k1_wellord1(sK11,X0)) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X1,X0),sK11) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5821,plain,
% 19.52/2.98      ( X0 = X1
% 19.52/2.98      | r2_hidden(X0,k1_wellord1(sK11,X1)) = iProver_top
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3490,c_3487]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_36,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 19.52/2.98      | r2_hidden(X3,k1_wellord1(X1,X2))
% 19.52/2.98      | ~ r2_hidden(X2,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X3,X0),X1)
% 19.52/2.98      | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
% 19.52/2.98      | ~ v2_wellord1(X1)
% 19.52/2.98      | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f109]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_621,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 19.52/2.98      | r2_hidden(X3,k1_wellord1(X1,X2))
% 19.52/2.98      | ~ r2_hidden(X2,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X3,X0),X1)
% 19.52/2.98      | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
% 19.52/2.98      | ~ v1_relat_1(X1)
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_36,c_42]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_622,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X1))
% 19.52/2.98      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 19.52/2.98      | ~ r1_tarski(k1_wellord1(sK11,X1),k3_relat_1(sK11))
% 19.52/2.98      | ~ v1_relat_1(sK11) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_621]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_624,plain,
% 19.52/2.98      ( ~ r1_tarski(k1_wellord1(sK11,X1),k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 19.52/2.98      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X1))
% 19.52/2.98      | ~ r2_hidden(X0,k1_wellord1(sK11,X1)) ),
% 19.52/2.98      inference(global_propositional_subsumption,[status(thm)],[c_622,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_625,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X1))
% 19.52/2.98      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 19.52/2.98      | ~ r1_tarski(k1_wellord1(sK11,X1),k3_relat_1(sK11)) ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_624]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_1056,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X1))
% 19.52/2.98      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X2,X0),sK11) ),
% 19.52/2.98      inference(backward_subsumption_resolution,[status(thm)],[c_958,c_625]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3480,plain,
% 19.52/2.98      ( r2_hidden(X0,k1_wellord1(sK11,X1)) != iProver_top
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X1)) = iProver_top
% 19.52/2.98      | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4158,plain,
% 19.52/2.98      ( r2_hidden(X0,k1_wellord1(sK11,X1)) = iProver_top
% 19.52/2.98      | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,sK0(k1_wellord1(sK11,X1),X2)),sK11) != iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X1),X2) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3508,c_3480]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7186,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,X0),X1) = X2
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
% 19.52/2.98      | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3490,c_4158]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f64]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_935,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_4,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_936,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_935]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3486,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5944,plain,
% 19.52/2.98      ( r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_4851,c_3486]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_49706,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
% 19.52/2.98      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | sK0(k1_wellord1(sK11,X0),X1) = X2
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_7186,c_5944,c_5946]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_49707,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,X0),X1) = X2
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
% 19.52/2.98      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_49706]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_49715,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,X0),X1) = X2
% 19.52/2.98      | r2_hidden(X2,k1_wellord1(sK11,X0)) = iProver_top
% 19.52/2.98      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k1_wellord1(sK11,X2)) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_49707,c_3487]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_56702,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = X1
% 19.52/2.98      | r2_hidden(X1,k1_wellord1(sK11,X0)) = iProver_top
% 19.52/2.98      | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_49715,c_3509]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_38,negated_conjecture,
% 19.52/2.98      ( ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
% 19.52/2.98      | ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 19.52/2.98      inference(cnf_transformation,[],[f104]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3505,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76114,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
% 19.52/2.98      | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top
% 19.52/2.98      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
% 19.52/2.98      | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_56702,c_3505]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_41,negated_conjecture,
% 19.52/2.98      ( r2_hidden(sK9,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(cnf_transformation,[],[f101]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_46,plain,
% 19.52/2.98      ( r2_hidden(sK9,k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_40,negated_conjecture,
% 19.52/2.98      ( r2_hidden(sK10,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(cnf_transformation,[],[f102]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_47,plain,
% 19.52/2.98      ( r2_hidden(sK10,k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_11,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f108]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_901,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_11,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_902,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(sK11,X0)) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_901]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5324,plain,
% 19.52/2.98      ( ~ r2_hidden(sK9,k1_wellord1(sK11,sK9)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_902]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5325,plain,
% 19.52/2.98      ( r2_hidden(sK9,k1_wellord1(sK11,sK9)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_5324]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3653,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(sK11,sK9))
% 19.52/2.98      | r2_hidden(X1,k1_wellord1(sK11,sK9))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 19.52/2.98      | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_1056]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_11330,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k1_wellord1(sK11,sK9))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(sK9,X0),sK11)
% 19.52/2.98      | r2_hidden(sK9,k1_wellord1(sK11,sK9))
% 19.52/2.98      | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_3653]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_22235,plain,
% 19.52/2.98      ( ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
% 19.52/2.98      | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9))
% 19.52/2.98      | r2_hidden(sK9,k1_wellord1(sK11,sK9))
% 19.52/2.98      | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_11330]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_22236,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top
% 19.52/2.98      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top
% 19.52/2.98      | r2_hidden(sK9,k1_wellord1(sK11,sK9)) = iProver_top
% 19.52/2.98      | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_22235]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76200,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
% 19.52/2.98      | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_76114,c_46,c_47,c_5325,c_22236]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76212,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
% 19.52/2.98      | sK10 = sK9
% 19.52/2.98      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
% 19.52/2.98      | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_5821,c_76200]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_39,negated_conjecture,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK10),sK11)
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 19.52/2.98      inference(cnf_transformation,[],[f103]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5203,plain,
% 19.52/2.98      ( ~ r2_hidden(sK10,k1_wellord1(sK11,sK10)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_902]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3586,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1)
% 19.52/2.98      | r2_hidden(X0,k1_wellord1(sK11,X0))
% 19.52/2.98      | ~ r1_tarski(X1,k1_wellord1(sK11,X0)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_2]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5213,plain,
% 19.52/2.98      ( ~ r2_hidden(sK10,k1_wellord1(sK11,X0))
% 19.52/2.98      | r2_hidden(sK10,k1_wellord1(sK11,sK10))
% 19.52/2.98      | ~ r1_tarski(k1_wellord1(sK11,X0),k1_wellord1(sK11,sK10)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_3586]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_21859,plain,
% 19.52/2.98      ( r2_hidden(sK10,k1_wellord1(sK11,sK10))
% 19.52/2.98      | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9))
% 19.52/2.98      | ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_5213]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76202,plain,
% 19.52/2.98      ( ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
% 19.52/2.98      | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10 ),
% 19.52/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_76200]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76217,plain,
% 19.52/2.98      ( r2_hidden(sK10,k1_wellord1(sK11,sK9))
% 19.52/2.98      | ~ r2_hidden(sK10,k3_relat_1(sK11))
% 19.52/2.98      | ~ r2_hidden(sK9,k3_relat_1(sK11))
% 19.52/2.98      | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
% 19.52/2.98      | sK10 = sK9 ),
% 19.52/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_76212]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76278,plain,
% 19.52/2.98      ( sK10 = sK9 | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10 ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_76212,c_41,c_40,c_39,c_5203,c_21859,c_76202,c_76217]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76279,plain,
% 19.52/2.98      ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10 | sK10 = sK9 ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_76278]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_76296,plain,
% 19.52/2.98      ( sK10 = sK9
% 19.52/2.98      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_76279,c_3508]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_48,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK10),sK11) = iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_77083,plain,
% 19.52/2.98      ( sK10 = sK9
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_76296,c_46,c_48,c_5325,c_22236]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_77087,plain,
% 19.52/2.98      ( sK10 = sK9 | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_77083,c_3505]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_77135,plain,
% 19.52/2.98      ( sK10 = sK9
% 19.52/2.98      | r2_hidden(sK9,sK4(sK11,sK10)) = iProver_top
% 19.52/2.98      | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3491,c_77087]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5204,plain,
% 19.52/2.98      ( r2_hidden(sK10,k1_wellord1(sK11,sK10)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_5203]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_21860,plain,
% 19.52/2.98      ( r2_hidden(sK10,k1_wellord1(sK11,sK10)) = iProver_top
% 19.52/2.98      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_21859]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_77137,plain,
% 19.52/2.98      ( sK10 = sK9
% 19.52/2.98      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top
% 19.52/2.98      | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_5821,c_77087]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_77477,plain,
% 19.52/2.98      ( sK10 = sK9 ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_77135,c_46,c_47,c_5204,c_21860,c_77083,c_77137]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_77542,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK9),sK11) != iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK9)) != iProver_top ),
% 19.52/2.98      inference(demodulation,[status(thm)],[c_77477,c_3505]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_78108,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK9),sK11) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_4166,c_77542]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_78118,plain,
% 19.52/2.98      ( r2_hidden(sK9,sK4(sK11,sK9)) = iProver_top
% 19.52/2.98      | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3491,c_78108]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3631,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,X0),sK11)
% 19.52/2.98      | r2_hidden(sK9,sK4(sK11,X0))
% 19.52/2.98      | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_860]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4416,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK9),sK11)
% 19.52/2.98      | r2_hidden(sK9,sK4(sK11,sK9))
% 19.52/2.98      | ~ r2_hidden(sK9,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_3631]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4419,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK9,sK9),sK11) = iProver_top
% 19.52/2.98      | r2_hidden(sK9,sK4(sK11,sK9)) = iProver_top
% 19.52/2.98      | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_4416]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_78184,plain,
% 19.52/2.98      ( r2_hidden(sK9,sK4(sK11,sK9)) = iProver_top ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_78118,c_46,c_4419,c_78108]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_27,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1)
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(X2,X1),X0),X2)
% 19.52/2.98      | ~ r1_tarski(X1,k3_relat_1(X2))
% 19.52/2.98      | ~ v2_wellord1(X2)
% 19.52/2.98      | ~ v1_relat_1(X2)
% 19.52/2.98      | k1_xboole_0 = X1 ),
% 19.52/2.98      inference(cnf_transformation,[],[f89]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_597,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1)
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(X2,X1),X0),X2)
% 19.52/2.98      | ~ r1_tarski(X1,k3_relat_1(X2))
% 19.52/2.98      | ~ v1_relat_1(X2)
% 19.52/2.98      | sK11 != X2
% 19.52/2.98      | k1_xboole_0 = X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_27,c_42]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_598,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1)
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(sK11,X1),X0),sK11)
% 19.52/2.98      | ~ r1_tarski(X1,k3_relat_1(sK11))
% 19.52/2.98      | ~ v1_relat_1(sK11)
% 19.52/2.98      | k1_xboole_0 = X1 ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_597]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_602,plain,
% 19.52/2.98      ( ~ r1_tarski(X1,k3_relat_1(sK11))
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(sK11,X1),X0),sK11)
% 19.52/2.98      | ~ r2_hidden(X0,X1)
% 19.52/2.98      | k1_xboole_0 = X1 ),
% 19.52/2.98      inference(global_propositional_subsumption,[status(thm)],[c_598,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_603,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,X1)
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(sK11,X1),X0),sK11)
% 19.52/2.98      | ~ r1_tarski(X1,k3_relat_1(sK11))
% 19.52/2.98      | k1_xboole_0 = X1 ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_602]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3500,plain,
% 19.52/2.98      ( k1_xboole_0 = X0
% 19.52/2.98      | r2_hidden(X1,X0) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(sK11,X0),X1),sK11) = iProver_top
% 19.52/2.98      | r1_tarski(X0,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_25,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,sK4(X1,X2))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f86]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_847,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,sK4(X1,X2))
% 19.52/2.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_25,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_848,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,sK4(sK11,X1)) | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_847]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3492,plain,
% 19.52/2.98      ( r2_hidden(X0,sK4(sK11,X1)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5408,plain,
% 19.52/2.98      ( sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(sK11,sK4(sK11,X0)),X0),sK11) != iProver_top
% 19.52/2.98      | r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3501,c_3492]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_26,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,sK4(X1,X2))
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | ~ v1_relat_1(X1) ),
% 19.52/2.98      inference(cnf_transformation,[],[f85]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_835,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,sK4(X1,X2))
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(X1))
% 19.52/2.98      | sK11 != X1 ),
% 19.52/2.98      inference(resolution_lifted,[status(thm)],[c_26,c_43]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_836,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,sK4(sK11,X1)) | r2_hidden(X0,k3_relat_1(sK11)) ),
% 19.52/2.98      inference(unflattening,[status(thm)],[c_835]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3493,plain,
% 19.52/2.98      ( r2_hidden(X0,sK4(sK11,X1)) != iProver_top
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4613,plain,
% 19.52/2.98      ( r2_hidden(sK0(sK4(sK11,X0),X1),k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r1_tarski(sK4(sK11,X0),X1) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3508,c_3493]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5302,plain,
% 19.52/2.98      ( r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_4613,c_3509]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7733,plain,
% 19.52/2.98      ( r2_hidden(k4_tarski(sK5(sK11,sK4(sK11,X0)),X0),sK11) != iProver_top
% 19.52/2.98      | sK4(sK11,X0) = k1_xboole_0 ),
% 19.52/2.98      inference(global_propositional_subsumption,[status(thm)],[c_5408,c_5302]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7734,plain,
% 19.52/2.98      ( sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(k4_tarski(sK5(sK11,sK4(sK11,X0)),X0),sK11) != iProver_top ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_7733]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7739,plain,
% 19.52/2.98      ( sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(X0,sK4(sK11,X0)) != iProver_top
% 19.52/2.98      | r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3500,c_7734]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7753,plain,
% 19.52/2.98      ( r2_hidden(X0,sK4(sK11,X0)) != iProver_top
% 19.52/2.98      | sK4(sK11,X0) = k1_xboole_0 ),
% 19.52/2.98      inference(global_propositional_subsumption,[status(thm)],[c_7739,c_5302]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7754,plain,
% 19.52/2.98      ( sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(X0,sK4(sK11,X0)) != iProver_top ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_7753]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_78192,plain,
% 19.52/2.98      ( sK4(sK11,sK9) = k1_xboole_0 ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_78184,c_7754]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_78193,plain,
% 19.52/2.98      ( r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 19.52/2.98      inference(demodulation,[status(thm)],[c_78192,c_78184]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_78206,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_62876,c_959,c_3714,c_4510,c_5285,c_8067,c_39313,c_78193]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_3484,plain,
% 19.52/2.98      ( r1_tarski(k1_wellord1(sK11,X0),k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_7742,plain,
% 19.52/2.98      ( sK5(sK11,sK4(sK11,X0)) = X0
% 19.52/2.98      | sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(sK5(sK11,sK4(sK11,X0)),k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,sK5(sK11,sK4(sK11,X0))),sK11) = iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3490,c_7734]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5409,plain,
% 19.52/2.98      ( sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(sK5(sK11,sK4(sK11,X0)),k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r1_tarski(sK4(sK11,X0),k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3501,c_3493]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_61479,plain,
% 19.52/2.98      ( r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | sK5(sK11,sK4(sK11,X0)) = X0
% 19.52/2.98      | r2_hidden(k4_tarski(X0,sK5(sK11,sK4(sK11,X0))),sK11) = iProver_top ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_7742,c_5302,c_5409]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_61480,plain,
% 19.52/2.98      ( sK5(sK11,sK4(sK11,X0)) = X0
% 19.52/2.98      | sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r2_hidden(k4_tarski(X0,sK5(sK11,sK4(sK11,X0))),sK11) = iProver_top ),
% 19.52/2.98      inference(renaming,[status(thm)],[c_61479]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_61491,plain,
% 19.52/2.98      ( sK5(sK11,sK4(sK11,X0)) = X0
% 19.52/2.98      | sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(X0,k1_wellord1(sK11,sK5(sK11,sK4(sK11,X0)))) = iProver_top
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_61480,c_3487]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_61922,plain,
% 19.52/2.98      ( sK5(sK11,sK4(sK11,X0)) = X0
% 19.52/2.98      | sK4(sK11,X0) = k1_xboole_0
% 19.52/2.98      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r1_tarski(k1_wellord1(sK11,sK5(sK11,sK4(sK11,X0))),X0) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_61491,c_3506]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_66927,plain,
% 19.52/2.98      ( sK5(sK11,sK4(sK11,k3_relat_1(sK11))) = k3_relat_1(sK11)
% 19.52/2.98      | sK4(sK11,k3_relat_1(sK11)) = k1_xboole_0
% 19.52/2.98      | r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_3484,c_61922]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5025,plain,
% 19.52/2.98      ( ~ r2_hidden(sK0(k3_relat_1(sK11),X0),X0)
% 19.52/2.98      | r1_tarski(k3_relat_1(sK11),X0) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_0]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_8192,plain,
% 19.52/2.98      ( ~ r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11))
% 19.52/2.98      | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_5025]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_8194,plain,
% 19.52/2.98      ( r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_8192]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_5026,plain,
% 19.52/2.98      ( r2_hidden(sK0(k3_relat_1(sK11),X0),k3_relat_1(sK11))
% 19.52/2.98      | r1_tarski(k3_relat_1(sK11),X0) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_1]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_8193,plain,
% 19.52/2.98      ( r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11))
% 19.52/2.98      | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_5026]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_8196,plain,
% 19.52/2.98      ( r2_hidden(sK0(k3_relat_1(sK11),k3_relat_1(sK11)),k3_relat_1(sK11)) = iProver_top
% 19.52/2.98      | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) = iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_8193]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_4214,plain,
% 19.52/2.98      ( ~ r2_hidden(X0,k3_relat_1(sK11)) | ~ r1_tarski(k3_relat_1(sK11),X0) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_5]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_17464,plain,
% 19.52/2.98      ( ~ r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11))
% 19.52/2.98      | ~ r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) ),
% 19.52/2.98      inference(instantiation,[status(thm)],[c_4214]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_17469,plain,
% 19.52/2.98      ( r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top
% 19.52/2.98      | r1_tarski(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(predicate_to_equality,[status(thm)],[c_17464]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_67141,plain,
% 19.52/2.98      ( r2_hidden(k3_relat_1(sK11),k3_relat_1(sK11)) != iProver_top ),
% 19.52/2.98      inference(global_propositional_subsumption,
% 19.52/2.98                [status(thm)],
% 19.52/2.98                [c_66927,c_8194,c_8196,c_17469]) ).
% 19.52/2.98  
% 19.52/2.98  cnf(c_78220,plain,
% 19.52/2.98      ( $false ),
% 19.52/2.98      inference(superposition,[status(thm)],[c_78206,c_67141]) ).
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.52/2.98  
% 19.52/2.98  ------                               Statistics
% 19.52/2.98  
% 19.52/2.98  ------ General
% 19.52/2.98  
% 19.52/2.98  abstr_ref_over_cycles:                  0
% 19.52/2.98  abstr_ref_under_cycles:                 0
% 19.52/2.98  gc_basic_clause_elim:                   0
% 19.52/2.98  forced_gc_time:                         0
% 19.52/2.98  parsing_time:                           0.01
% 19.52/2.98  unif_index_cands_time:                  0.
% 19.52/2.98  unif_index_add_time:                    0.
% 19.52/2.98  orderings_time:                         0.
% 19.52/2.98  out_proof_time:                         0.029
% 19.52/2.98  total_time:                             2.312
% 19.52/2.98  num_of_symbols:                         56
% 19.52/2.98  num_of_terms:                           57107
% 19.52/2.98  
% 19.52/2.98  ------ Preprocessing
% 19.52/2.98  
% 19.52/2.98  num_of_splits:                          0
% 19.52/2.98  num_of_split_atoms:                     0
% 19.52/2.98  num_of_reused_defs:                     0
% 19.52/2.98  num_eq_ax_congr_red:                    40
% 19.52/2.98  num_of_sem_filtered_clauses:            1
% 19.52/2.98  num_of_subtypes:                        0
% 19.52/2.98  monotx_restored_types:                  0
% 19.52/2.98  sat_num_of_epr_types:                   0
% 19.52/2.98  sat_num_of_non_cyclic_types:            0
% 19.52/2.98  sat_guarded_non_collapsed_types:        0
% 19.52/2.98  num_pure_diseq_elim:                    0
% 19.52/2.98  simp_replaced_by:                       0
% 19.52/2.98  res_preprocessed:                       160
% 19.52/2.98  prep_upred:                             0
% 19.52/2.98  prep_unflattend:                        164
% 19.52/2.98  smt_new_axioms:                         0
% 19.52/2.98  pred_elim_cands:                        2
% 19.52/2.98  pred_elim:                              7
% 19.52/2.98  pred_elim_cl:                           13
% 19.52/2.98  pred_elim_cycles:                       9
% 19.52/2.98  merged_defs:                            8
% 19.52/2.98  merged_defs_ncl:                        0
% 19.52/2.98  bin_hyper_res:                          8
% 19.52/2.98  prep_cycles:                            4
% 19.52/2.98  pred_elim_time:                         0.042
% 19.52/2.98  splitting_time:                         0.
% 19.52/2.98  sem_filter_time:                        0.
% 19.52/2.98  monotx_time:                            0.
% 19.52/2.98  subtype_inf_time:                       0.
% 19.52/2.98  
% 19.52/2.98  ------ Problem properties
% 19.52/2.98  
% 19.52/2.98  clauses:                                30
% 19.52/2.98  conjectures:                            4
% 19.52/2.98  epr:                                    2
% 19.52/2.98  horn:                                   14
% 19.52/2.98  ground:                                 4
% 19.52/2.98  unary:                                  4
% 19.52/2.98  binary:                                 10
% 19.52/2.98  lits:                                   83
% 19.52/2.98  lits_eq:                                18
% 19.52/2.98  fd_pure:                                0
% 19.52/2.98  fd_pseudo:                              0
% 19.52/2.98  fd_cond:                                5
% 19.52/2.98  fd_pseudo_cond:                         4
% 19.52/2.98  ac_symbols:                             0
% 19.52/2.98  
% 19.52/2.98  ------ Propositional Solver
% 19.52/2.98  
% 19.52/2.98  prop_solver_calls:                      37
% 19.52/2.98  prop_fast_solver_calls:                 4117
% 19.52/2.98  smt_solver_calls:                       0
% 19.52/2.98  smt_fast_solver_calls:                  0
% 19.52/2.98  prop_num_of_clauses:                    30480
% 19.52/2.98  prop_preprocess_simplified:             51124
% 19.52/2.98  prop_fo_subsumed:                       152
% 19.52/2.98  prop_solver_time:                       0.
% 19.52/2.98  smt_solver_time:                        0.
% 19.52/2.98  smt_fast_solver_time:                   0.
% 19.52/2.98  prop_fast_solver_time:                  0.
% 19.52/2.98  prop_unsat_core_time:                   0.
% 19.52/2.98  
% 19.52/2.98  ------ QBF
% 19.52/2.98  
% 19.52/2.98  qbf_q_res:                              0
% 19.52/2.98  qbf_num_tautologies:                    0
% 19.52/2.98  qbf_prep_cycles:                        0
% 19.52/2.98  
% 19.52/2.98  ------ BMC1
% 19.52/2.98  
% 19.52/2.98  bmc1_current_bound:                     -1
% 19.52/2.98  bmc1_last_solved_bound:                 -1
% 19.52/2.98  bmc1_unsat_core_size:                   -1
% 19.52/2.98  bmc1_unsat_core_parents_size:           -1
% 19.52/2.98  bmc1_merge_next_fun:                    0
% 19.52/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.52/2.98  
% 19.52/2.98  ------ Instantiation
% 19.52/2.98  
% 19.52/2.98  inst_num_of_clauses:                    513
% 19.52/2.98  inst_num_in_passive:                    287
% 19.52/2.98  inst_num_in_active:                     2220
% 19.52/2.98  inst_num_in_unprocessed:                33
% 19.52/2.98  inst_num_of_loops:                      3209
% 19.52/2.98  inst_num_of_learning_restarts:          1
% 19.52/2.98  inst_num_moves_active_passive:          987
% 19.52/2.98  inst_lit_activity:                      0
% 19.52/2.98  inst_lit_activity_moves:                0
% 19.52/2.98  inst_num_tautologies:                   0
% 19.52/2.98  inst_num_prop_implied:                  0
% 19.52/2.98  inst_num_existing_simplified:           0
% 19.52/2.98  inst_num_eq_res_simplified:             0
% 19.52/2.98  inst_num_child_elim:                    0
% 19.52/2.98  inst_num_of_dismatching_blockings:      10281
% 19.52/2.98  inst_num_of_non_proper_insts:           8585
% 19.52/2.98  inst_num_of_duplicates:                 0
% 19.52/2.98  inst_inst_num_from_inst_to_res:         0
% 19.52/2.98  inst_dismatching_checking_time:         0.
% 19.52/2.98  
% 19.52/2.98  ------ Resolution
% 19.52/2.98  
% 19.52/2.98  res_num_of_clauses:                     43
% 19.52/2.98  res_num_in_passive:                     43
% 19.52/2.98  res_num_in_active:                      0
% 19.52/2.98  res_num_of_loops:                       164
% 19.52/2.98  res_forward_subset_subsumed:            664
% 19.52/2.98  res_backward_subset_subsumed:           20
% 19.52/2.98  res_forward_subsumed:                   0
% 19.52/2.98  res_backward_subsumed:                  16
% 19.52/2.98  res_forward_subsumption_resolution:     0
% 19.52/2.98  res_backward_subsumption_resolution:    1
% 19.52/2.98  res_clause_to_clause_subsumption:       34181
% 19.52/2.98  res_orphan_elimination:                 0
% 19.52/2.98  res_tautology_del:                      861
% 19.52/2.98  res_num_eq_res_simplified:              0
% 19.52/2.98  res_num_sel_changes:                    0
% 19.52/2.98  res_moves_from_active_to_pass:          0
% 19.52/2.98  
% 19.52/2.98  ------ Superposition
% 19.52/2.98  
% 19.52/2.98  sup_time_total:                         0.
% 19.52/2.98  sup_time_generating:                    0.
% 19.52/2.98  sup_time_sim_full:                      0.
% 19.52/2.98  sup_time_sim_immed:                     0.
% 19.52/2.98  
% 19.52/2.98  sup_num_of_clauses:                     2641
% 19.52/2.98  sup_num_in_active:                      337
% 19.52/2.98  sup_num_in_passive:                     2304
% 19.52/2.98  sup_num_of_loops:                       641
% 19.52/2.98  sup_fw_superposition:                   2611
% 19.52/2.98  sup_bw_superposition:                   3427
% 19.52/2.98  sup_immediate_simplified:               1967
% 19.52/2.98  sup_given_eliminated:                   5
% 19.52/2.98  comparisons_done:                       0
% 19.52/2.98  comparisons_avoided:                    31
% 19.52/2.98  
% 19.52/2.98  ------ Simplifications
% 19.52/2.98  
% 19.52/2.98  
% 19.52/2.98  sim_fw_subset_subsumed:                 711
% 19.52/2.98  sim_bw_subset_subsumed:                 277
% 19.52/2.98  sim_fw_subsumed:                        918
% 19.52/2.98  sim_bw_subsumed:                        264
% 19.52/2.98  sim_fw_subsumption_res:                 0
% 19.52/2.98  sim_bw_subsumption_res:                 0
% 19.52/2.98  sim_tautology_del:                      97
% 19.52/2.98  sim_eq_tautology_del:                   81
% 19.52/2.98  sim_eq_res_simp:                        9
% 19.52/2.98  sim_fw_demodulated:                     161
% 19.52/2.98  sim_bw_demodulated:                     68
% 19.52/2.98  sim_light_normalised:                   72
% 19.52/2.98  sim_joinable_taut:                      0
% 19.52/2.98  sim_joinable_simp:                      0
% 19.52/2.98  sim_ac_normalised:                      0
% 19.52/2.98  sim_smt_subsumption:                    0
% 19.52/2.98  
%------------------------------------------------------------------------------
