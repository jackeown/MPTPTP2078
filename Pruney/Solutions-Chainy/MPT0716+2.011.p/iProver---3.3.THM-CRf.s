%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:53 EST 2020

% Result     : Theorem 47.81s
% Output     : CNFRefutation 47.81s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 924 expanded)
%              Number of clauses        :   92 ( 227 expanded)
%              Number of leaves         :   17 ( 250 expanded)
%              Depth                    :   22
%              Number of atoms          :  529 (6087 expanded)
%              Number of equality atoms :  110 ( 228 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
            | ~ r1_tarski(X2,k1_relat_1(X0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
          & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1))
          | ~ r1_tarski(sK3,k1_relat_1(X0))
          | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1))
            & r1_tarski(sK3,k1_relat_1(X0)) )
          | r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))) ) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK1))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK1)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
      | ~ r1_tarski(sK3,k1_relat_1(sK1))
      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) )
    & ( ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
        & r1_tarski(sK3,k1_relat_1(sK1)) )
      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).

fof(f54,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_174,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_173,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2094,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_174,c_173])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4514,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
    inference(resolution,[status(thm)],[c_2094,c_6])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2115,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_175,c_173])).

cnf(c_22979,plain,
    ( ~ r1_tarski(k10_relat_1(X0,k1_relat_1(X1)),X2)
    | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4514,c_2115])).

cnf(c_2111,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k1_relat_1(X2)))
    | ~ r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | X0 != X3 ),
    inference(resolution,[status(thm)],[c_175,c_6])).

cnf(c_8,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3318,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2297,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_2115,c_4])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2324,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_2297,c_3])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2544,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),X0)
    | r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_2324,c_14])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_703,plain,
    ( r2_hidden(sK0(sK3,k1_relat_1(sK1)),sK3)
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_801,plain,
    ( r2_hidden(sK0(sK3,k1_relat_1(sK1)),X0)
    | ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_986,plain,
    ( r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),sK3)
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1344,plain,
    ( ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK1,sK2)))
    | r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1529,plain,
    ( ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(sK1))
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2563,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2544,c_18,c_17,c_16,c_15,c_14,c_703,c_986,c_1344,c_1529])).

cnf(c_505,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_510,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3198,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_510])).

cnf(c_500,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_502,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_512,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2068,plain,
    ( k10_relat_1(X0,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(X0,sK2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_512])).

cnf(c_2268,plain,
    ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_500,c_2068])).

cnf(c_3238,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3198,c_2268])).

cnf(c_3266,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3238])).

cnf(c_3697,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3318,c_18,c_17,c_16,c_15,c_14,c_703,c_986,c_1344,c_1529,c_3266])).

cnf(c_12999,plain,
    ( r1_tarski(X0,k10_relat_1(sK1,k1_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_2111,c_3697])).

cnf(c_13567,plain,
    ( r1_tarski(X0,k10_relat_1(sK1,k1_relat_1(sK2)))
    | X0 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12999,c_18,c_16])).

cnf(c_178417,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k10_relat_1(sK1,k1_relat_1(sK2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_relat_1(X1)) != sK3 ),
    inference(resolution,[status(thm)],[c_22979,c_13567])).

cnf(c_2301,plain,
    ( r1_tarski(k10_relat_1(X0,k1_relat_1(X1)),X2)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_2115,c_6])).

cnf(c_13768,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k10_relat_1(sK1,k1_relat_1(sK2)),X1)
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_13567,c_2324])).

cnf(c_32678,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),X1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_2301,c_13768])).

cnf(c_35446,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),X1)
    | X0 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32678,c_18,c_16])).

cnf(c_178894,plain,
    ( r1_tarski(X0,k10_relat_1(sK1,k1_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | X0 != sK3
    | k10_relat_1(sK1,k1_relat_1(sK2)) != sK3 ),
    inference(resolution,[status(thm)],[c_178417,c_35446])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_811,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_749,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),k9_relat_1(X0,X1))
    | r1_tarski(k9_relat_1(X0,X1),X2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_824,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
    | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1401,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
    | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
    | ~ r1_tarski(k9_relat_1(sK1,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1594,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,X0))
    | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
    | ~ r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1595,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,X0))
    | ~ r1_tarski(sK3,X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1971,plain,
    ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_977,plain,
    ( r2_hidden(sK0(sK3,X0),sK3)
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3040,plain,
    ( r2_hidden(sK0(sK3,sK3),sK3)
    | r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_3041,plain,
    ( ~ r2_hidden(sK0(sK3,sK3),sK3)
    | r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_989,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_1987,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_6983,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK3)
    | X0 != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_852,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(X3))
    | X2 != X0
    | k1_relat_1(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_1093,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | r1_tarski(X2,k1_relat_1(X1))
    | X2 != X0
    | k1_relat_1(X1) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_7190,plain,
    ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | X0 != sK3
    | k1_relat_1(k5_relat_1(sK1,sK2)) != k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_180,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_7381,plain,
    ( k5_relat_1(sK1,sK2) != X0
    | k1_relat_1(k5_relat_1(sK1,sK2)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_18470,plain,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2)
    | k1_relat_1(k5_relat_1(sK1,sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7381])).

cnf(c_17484,plain,
    ( ~ r2_hidden(sK0(X0,k1_relat_1(X1)),k1_relat_1(X1))
    | r1_tarski(X0,k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_46121,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
    | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_17484])).

cnf(c_513,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_511,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_517,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_516,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1932,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_517,c_516])).

cnf(c_8974,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1932,c_516])).

cnf(c_29260,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k9_relat_1(X3,k10_relat_1(X3,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_511,c_8974])).

cnf(c_75100,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),X3) = iProver_top
    | r1_tarski(X1,k10_relat_1(X0,X3)) != iProver_top
    | r1_tarski(k9_relat_1(X0,X1),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_29260])).

cnf(c_518,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_90453,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_75100,c_518])).

cnf(c_90747,plain,
    ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_90453])).

cnf(c_91188,plain,
    ( ~ r1_tarski(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_90747])).

cnf(c_15286,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
    | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_46120,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
    | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_15286])).

cnf(c_174330,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,X0))
    | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_46120])).

cnf(c_185889,plain,
    ( X0 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_178894,c_18,c_17,c_16,c_15,c_14,c_12,c_703,c_811,c_824,c_986,c_1344,c_1529,c_1594,c_1595,c_1971,c_3040,c_3041,c_3266,c_6983,c_7190,c_18470,c_46121,c_91188,c_174330])).

cnf(c_186731,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_185889,c_173])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:47:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 47.81/6.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.81/6.49  
% 47.81/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.81/6.49  
% 47.81/6.49  ------  iProver source info
% 47.81/6.49  
% 47.81/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.81/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.81/6.49  git: non_committed_changes: false
% 47.81/6.49  git: last_make_outside_of_git: false
% 47.81/6.49  
% 47.81/6.49  ------ 
% 47.81/6.49  ------ Parsing...
% 47.81/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.81/6.49  
% 47.81/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 47.81/6.49  
% 47.81/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.81/6.49  
% 47.81/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.81/6.49  ------ Proving...
% 47.81/6.49  ------ Problem Properties 
% 47.81/6.49  
% 47.81/6.49  
% 47.81/6.49  clauses                                 19
% 47.81/6.49  conjectures                             7
% 47.81/6.49  EPR                                     5
% 47.81/6.49  Horn                                    16
% 47.81/6.49  unary                                   4
% 47.81/6.49  binary                                  6
% 47.81/6.49  lits                                    55
% 47.81/6.49  lits eq                                 2
% 47.81/6.49  fd_pure                                 0
% 47.81/6.49  fd_pseudo                               0
% 47.81/6.49  fd_cond                                 0
% 47.81/6.49  fd_pseudo_cond                          0
% 47.81/6.49  AC symbols                              0
% 47.81/6.49  
% 47.81/6.49  ------ Input Options Time Limit: Unbounded
% 47.81/6.49  
% 47.81/6.49  
% 47.81/6.49  ------ 
% 47.81/6.49  Current options:
% 47.81/6.49  ------ 
% 47.81/6.49  
% 47.81/6.49  
% 47.81/6.49  
% 47.81/6.49  
% 47.81/6.49  ------ Proving...
% 47.81/6.49  
% 47.81/6.49  
% 47.81/6.49  % SZS status Theorem for theBenchmark.p
% 47.81/6.49  
% 47.81/6.49   Resolution empty clause
% 47.81/6.49  
% 47.81/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.81/6.49  
% 47.81/6.49  fof(f5,axiom,(
% 47.81/6.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f16,plain,(
% 47.81/6.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 47.81/6.49    inference(ennf_transformation,[],[f5])).
% 47.81/6.49  
% 47.81/6.49  fof(f43,plain,(
% 47.81/6.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f16])).
% 47.81/6.49  
% 47.81/6.49  fof(f7,axiom,(
% 47.81/6.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f19,plain,(
% 47.81/6.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 47.81/6.49    inference(ennf_transformation,[],[f7])).
% 47.81/6.49  
% 47.81/6.49  fof(f20,plain,(
% 47.81/6.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 47.81/6.49    inference(flattening,[],[f19])).
% 47.81/6.49  
% 47.81/6.49  fof(f45,plain,(
% 47.81/6.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f20])).
% 47.81/6.49  
% 47.81/6.49  fof(f9,conjecture,(
% 47.81/6.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f10,negated_conjecture,(
% 47.81/6.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 47.81/6.49    inference(negated_conjecture,[],[f9])).
% 47.81/6.49  
% 47.81/6.49  fof(f23,plain,(
% 47.81/6.49    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 47.81/6.49    inference(ennf_transformation,[],[f10])).
% 47.81/6.49  
% 47.81/6.49  fof(f24,plain,(
% 47.81/6.49    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 47.81/6.49    inference(flattening,[],[f23])).
% 47.81/6.49  
% 47.81/6.49  fof(f31,plain,(
% 47.81/6.49    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 47.81/6.49    inference(nnf_transformation,[],[f24])).
% 47.81/6.49  
% 47.81/6.49  fof(f32,plain,(
% 47.81/6.49    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 47.81/6.49    inference(flattening,[],[f31])).
% 47.81/6.49  
% 47.81/6.49  fof(f35,plain,(
% 47.81/6.49    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1)) | ~r1_tarski(sK3,k1_relat_1(X0)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1)) & r1_tarski(sK3,k1_relat_1(X0))) | r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 47.81/6.49    introduced(choice_axiom,[])).
% 47.81/6.49  
% 47.81/6.49  fof(f34,plain,(
% 47.81/6.49    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))))) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 47.81/6.49    introduced(choice_axiom,[])).
% 47.81/6.49  
% 47.81/6.49  fof(f33,plain,(
% 47.81/6.49    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1)))) & ((r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK1))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 47.81/6.49    introduced(choice_axiom,[])).
% 47.81/6.49  
% 47.81/6.49  fof(f36,plain,(
% 47.81/6.49    (((~r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | ~r1_tarski(sK3,k1_relat_1(sK1)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))) & ((r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) & r1_tarski(sK3,k1_relat_1(sK1))) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 47.81/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).
% 47.81/6.49  
% 47.81/6.49  fof(f54,plain,(
% 47.81/6.49    r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 47.81/6.49    inference(cnf_transformation,[],[f36])).
% 47.81/6.49  
% 47.81/6.49  fof(f49,plain,(
% 47.81/6.49    v1_relat_1(sK1)),
% 47.81/6.49    inference(cnf_transformation,[],[f36])).
% 47.81/6.49  
% 47.81/6.49  fof(f50,plain,(
% 47.81/6.49    v1_funct_1(sK1)),
% 47.81/6.49    inference(cnf_transformation,[],[f36])).
% 47.81/6.49  
% 47.81/6.49  fof(f3,axiom,(
% 47.81/6.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f13,plain,(
% 47.81/6.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 47.81/6.49    inference(ennf_transformation,[],[f3])).
% 47.81/6.49  
% 47.81/6.49  fof(f41,plain,(
% 47.81/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f13])).
% 47.81/6.49  
% 47.81/6.49  fof(f2,axiom,(
% 47.81/6.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f12,plain,(
% 47.81/6.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 47.81/6.49    inference(ennf_transformation,[],[f2])).
% 47.81/6.49  
% 47.81/6.49  fof(f40,plain,(
% 47.81/6.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f12])).
% 47.81/6.49  
% 47.81/6.49  fof(f53,plain,(
% 47.81/6.49    r1_tarski(sK3,k1_relat_1(sK1)) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 47.81/6.49    inference(cnf_transformation,[],[f36])).
% 47.81/6.49  
% 47.81/6.49  fof(f51,plain,(
% 47.81/6.49    v1_relat_1(sK2)),
% 47.81/6.49    inference(cnf_transformation,[],[f36])).
% 47.81/6.49  
% 47.81/6.49  fof(f52,plain,(
% 47.81/6.49    v1_funct_1(sK2)),
% 47.81/6.49    inference(cnf_transformation,[],[f36])).
% 47.81/6.49  
% 47.81/6.49  fof(f1,axiom,(
% 47.81/6.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f11,plain,(
% 47.81/6.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 47.81/6.49    inference(ennf_transformation,[],[f1])).
% 47.81/6.49  
% 47.81/6.49  fof(f25,plain,(
% 47.81/6.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 47.81/6.49    inference(nnf_transformation,[],[f11])).
% 47.81/6.49  
% 47.81/6.49  fof(f26,plain,(
% 47.81/6.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 47.81/6.49    inference(rectify,[],[f25])).
% 47.81/6.49  
% 47.81/6.49  fof(f27,plain,(
% 47.81/6.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 47.81/6.49    introduced(choice_axiom,[])).
% 47.81/6.49  
% 47.81/6.49  fof(f28,plain,(
% 47.81/6.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 47.81/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 47.81/6.49  
% 47.81/6.49  fof(f38,plain,(
% 47.81/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f28])).
% 47.81/6.49  
% 47.81/6.49  fof(f37,plain,(
% 47.81/6.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f28])).
% 47.81/6.49  
% 47.81/6.49  fof(f8,axiom,(
% 47.81/6.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f21,plain,(
% 47.81/6.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 47.81/6.49    inference(ennf_transformation,[],[f8])).
% 47.81/6.49  
% 47.81/6.49  fof(f22,plain,(
% 47.81/6.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 47.81/6.49    inference(flattening,[],[f21])).
% 47.81/6.49  
% 47.81/6.49  fof(f29,plain,(
% 47.81/6.49    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 47.81/6.49    inference(nnf_transformation,[],[f22])).
% 47.81/6.49  
% 47.81/6.49  fof(f30,plain,(
% 47.81/6.49    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 47.81/6.49    inference(flattening,[],[f29])).
% 47.81/6.49  
% 47.81/6.49  fof(f46,plain,(
% 47.81/6.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f30])).
% 47.81/6.49  
% 47.81/6.49  fof(f39,plain,(
% 47.81/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f28])).
% 47.81/6.49  
% 47.81/6.49  fof(f55,plain,(
% 47.81/6.49    ~r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | ~r1_tarski(sK3,k1_relat_1(sK1)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 47.81/6.49    inference(cnf_transformation,[],[f36])).
% 47.81/6.49  
% 47.81/6.49  fof(f4,axiom,(
% 47.81/6.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f14,plain,(
% 47.81/6.49    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 47.81/6.49    inference(ennf_transformation,[],[f4])).
% 47.81/6.49  
% 47.81/6.49  fof(f15,plain,(
% 47.81/6.49    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 47.81/6.49    inference(flattening,[],[f14])).
% 47.81/6.49  
% 47.81/6.49  fof(f42,plain,(
% 47.81/6.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f15])).
% 47.81/6.49  
% 47.81/6.49  fof(f6,axiom,(
% 47.81/6.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 47.81/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.81/6.49  
% 47.81/6.49  fof(f17,plain,(
% 47.81/6.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 47.81/6.49    inference(ennf_transformation,[],[f6])).
% 47.81/6.49  
% 47.81/6.49  fof(f18,plain,(
% 47.81/6.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 47.81/6.49    inference(flattening,[],[f17])).
% 47.81/6.49  
% 47.81/6.49  fof(f44,plain,(
% 47.81/6.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 47.81/6.49    inference(cnf_transformation,[],[f18])).
% 47.81/6.49  
% 47.81/6.49  cnf(c_174,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_173,plain,( X0 = X0 ),theory(equality) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2094,plain,
% 47.81/6.49      ( X0 != X1 | X1 = X0 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_174,c_173]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_6,plain,
% 47.81/6.49      ( ~ v1_relat_1(X0)
% 47.81/6.49      | ~ v1_relat_1(X1)
% 47.81/6.49      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 47.81/6.49      inference(cnf_transformation,[],[f43]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_4514,plain,
% 47.81/6.49      ( ~ v1_relat_1(X0)
% 47.81/6.49      | ~ v1_relat_1(X1)
% 47.81/6.49      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_2094,c_6]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_175,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.81/6.49      theory(equality) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2115,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_175,c_173]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_22979,plain,
% 47.81/6.49      ( ~ r1_tarski(k10_relat_1(X0,k1_relat_1(X1)),X2)
% 47.81/6.49      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),X2)
% 47.81/6.49      | ~ v1_relat_1(X1)
% 47.81/6.49      | ~ v1_relat_1(X0) ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_4514,c_2115]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2111,plain,
% 47.81/6.49      ( r1_tarski(X0,k10_relat_1(X1,k1_relat_1(X2)))
% 47.81/6.49      | ~ r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
% 47.81/6.49      | ~ v1_relat_1(X2)
% 47.81/6.49      | ~ v1_relat_1(X1)
% 47.81/6.49      | X0 != X3 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_175,c_6]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_8,plain,
% 47.81/6.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 47.81/6.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 47.81/6.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 47.81/6.49      | ~ v1_funct_1(X1)
% 47.81/6.49      | ~ v1_relat_1(X1) ),
% 47.81/6.49      inference(cnf_transformation,[],[f45]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_13,negated_conjecture,
% 47.81/6.49      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 47.81/6.49      inference(cnf_transformation,[],[f54]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3318,plain,
% 47.81/6.49      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | ~ r1_tarski(sK3,k1_relat_1(sK1))
% 47.81/6.49      | ~ v1_funct_1(sK1)
% 47.81/6.49      | ~ v1_relat_1(sK1) ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_8,c_13]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_18,negated_conjecture,
% 47.81/6.49      ( v1_relat_1(sK1) ),
% 47.81/6.49      inference(cnf_transformation,[],[f49]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_17,negated_conjecture,
% 47.81/6.49      ( v1_funct_1(sK1) ),
% 47.81/6.49      inference(cnf_transformation,[],[f50]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_4,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 47.81/6.49      inference(cnf_transformation,[],[f41]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2297,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1)
% 47.81/6.49      | ~ r1_tarski(X2,X0)
% 47.81/6.49      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_2115,c_4]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3,plain,
% 47.81/6.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 47.81/6.49      inference(cnf_transformation,[],[f40]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2324,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_2297,c_3]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_14,negated_conjecture,
% 47.81/6.49      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 47.81/6.49      inference(cnf_transformation,[],[f53]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2544,plain,
% 47.81/6.49      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),X0)
% 47.81/6.49      | r1_tarski(sK3,X0)
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_2324,c_14]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_16,negated_conjecture,
% 47.81/6.49      ( v1_relat_1(sK2) ),
% 47.81/6.49      inference(cnf_transformation,[],[f51]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_15,negated_conjecture,
% 47.81/6.49      ( v1_funct_1(sK2) ),
% 47.81/6.49      inference(cnf_transformation,[],[f52]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1,plain,
% 47.81/6.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 47.81/6.49      inference(cnf_transformation,[],[f38]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_703,plain,
% 47.81/6.49      ( r2_hidden(sK0(sK3,k1_relat_1(sK1)),sK3)
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_1]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2,plain,
% 47.81/6.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 47.81/6.49      inference(cnf_transformation,[],[f37]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_801,plain,
% 47.81/6.49      ( r2_hidden(sK0(sK3,k1_relat_1(sK1)),X0)
% 47.81/6.49      | ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),sK3)
% 47.81/6.49      | ~ r1_tarski(sK3,X0) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_2]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_986,plain,
% 47.81/6.49      ( r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),sK3)
% 47.81/6.49      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_801]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_11,plain,
% 47.81/6.49      ( r2_hidden(X0,k1_relat_1(X1))
% 47.81/6.49      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 47.81/6.49      | ~ v1_funct_1(X2)
% 47.81/6.49      | ~ v1_funct_1(X1)
% 47.81/6.49      | ~ v1_relat_1(X1)
% 47.81/6.49      | ~ v1_relat_1(X2) ),
% 47.81/6.49      inference(cnf_transformation,[],[f46]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1344,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(sK1))
% 47.81/6.49      | ~ v1_funct_1(sK2)
% 47.81/6.49      | ~ v1_funct_1(sK1)
% 47.81/6.49      | ~ v1_relat_1(sK2)
% 47.81/6.49      | ~ v1_relat_1(sK1) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_11]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_0,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 47.81/6.49      inference(cnf_transformation,[],[f39]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1529,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(sK3,k1_relat_1(sK1)),k1_relat_1(sK1))
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_0]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2563,plain,
% 47.81/6.49      ( r1_tarski(sK3,k1_relat_1(sK1)) ),
% 47.81/6.49      inference(global_propositional_subsumption,
% 47.81/6.49                [status(thm)],
% 47.81/6.49                [c_2544,c_18,c_17,c_16,c_15,c_14,c_703,c_986,c_1344,c_1529]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_505,plain,
% 47.81/6.49      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_510,plain,
% 47.81/6.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 47.81/6.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 47.81/6.49      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 47.81/6.49      | v1_funct_1(X1) != iProver_top
% 47.81/6.49      | v1_relat_1(X1) != iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3198,plain,
% 47.81/6.49      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
% 47.81/6.49      | v1_funct_1(sK1) != iProver_top
% 47.81/6.49      | v1_relat_1(sK1) != iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_505,c_510]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_500,plain,
% 47.81/6.49      ( v1_relat_1(sK1) = iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_502,plain,
% 47.81/6.49      ( v1_relat_1(sK2) = iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_512,plain,
% 47.81/6.49      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 47.81/6.49      | v1_relat_1(X0) != iProver_top
% 47.81/6.49      | v1_relat_1(X1) != iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2068,plain,
% 47.81/6.49      ( k10_relat_1(X0,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(X0,sK2))
% 47.81/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_502,c_512]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2268,plain,
% 47.81/6.49      ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_500,c_2068]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3238,plain,
% 47.81/6.49      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
% 47.81/6.49      | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
% 47.81/6.49      | v1_funct_1(sK1) != iProver_top
% 47.81/6.49      | v1_relat_1(sK1) != iProver_top ),
% 47.81/6.49      inference(light_normalisation,[status(thm)],[c_3198,c_2268]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3266,plain,
% 47.81/6.49      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | ~ r1_tarski(sK3,k1_relat_1(sK1))
% 47.81/6.49      | ~ v1_funct_1(sK1)
% 47.81/6.49      | ~ v1_relat_1(sK1) ),
% 47.81/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_3238]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3697,plain,
% 47.81/6.49      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 47.81/6.49      inference(global_propositional_subsumption,
% 47.81/6.49                [status(thm)],
% 47.81/6.49                [c_3318,c_18,c_17,c_16,c_15,c_14,c_703,c_986,c_1344,c_1529,
% 47.81/6.49                 c_3266]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_12999,plain,
% 47.81/6.49      ( r1_tarski(X0,k10_relat_1(sK1,k1_relat_1(sK2)))
% 47.81/6.49      | ~ v1_relat_1(sK2)
% 47.81/6.49      | ~ v1_relat_1(sK1)
% 47.81/6.49      | X0 != sK3 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_2111,c_3697]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_13567,plain,
% 47.81/6.49      ( r1_tarski(X0,k10_relat_1(sK1,k1_relat_1(sK2))) | X0 != sK3 ),
% 47.81/6.49      inference(global_propositional_subsumption,
% 47.81/6.49                [status(thm)],
% 47.81/6.49                [c_12999,c_18,c_16]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_178417,plain,
% 47.81/6.49      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k10_relat_1(sK1,k1_relat_1(sK2)))
% 47.81/6.49      | ~ v1_relat_1(X1)
% 47.81/6.49      | ~ v1_relat_1(X0)
% 47.81/6.49      | k10_relat_1(X0,k1_relat_1(X1)) != sK3 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_22979,c_13567]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_2301,plain,
% 47.81/6.49      ( r1_tarski(k10_relat_1(X0,k1_relat_1(X1)),X2)
% 47.81/6.49      | ~ r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),X2)
% 47.81/6.49      | ~ v1_relat_1(X1)
% 47.81/6.49      | ~ v1_relat_1(X0) ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_2115,c_6]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_13768,plain,
% 47.81/6.49      ( r1_tarski(X0,X1)
% 47.81/6.49      | ~ r1_tarski(k10_relat_1(sK1,k1_relat_1(sK2)),X1)
% 47.81/6.49      | X0 != sK3 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_13567,c_2324]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_32678,plain,
% 47.81/6.49      ( r1_tarski(X0,X1)
% 47.81/6.49      | ~ r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),X1)
% 47.81/6.49      | ~ v1_relat_1(sK2)
% 47.81/6.49      | ~ v1_relat_1(sK1)
% 47.81/6.49      | X0 != sK3 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_2301,c_13768]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_35446,plain,
% 47.81/6.49      ( r1_tarski(X0,X1)
% 47.81/6.49      | ~ r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),X1)
% 47.81/6.49      | X0 != sK3 ),
% 47.81/6.49      inference(global_propositional_subsumption,
% 47.81/6.49                [status(thm)],
% 47.81/6.49                [c_32678,c_18,c_16]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_178894,plain,
% 47.81/6.49      ( r1_tarski(X0,k10_relat_1(sK1,k1_relat_1(sK2)))
% 47.81/6.49      | ~ v1_relat_1(sK2)
% 47.81/6.49      | ~ v1_relat_1(sK1)
% 47.81/6.49      | X0 != sK3
% 47.81/6.49      | k10_relat_1(sK1,k1_relat_1(sK2)) != sK3 ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_178417,c_35446]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_12,negated_conjecture,
% 47.81/6.49      ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
% 47.81/6.49      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | ~ r1_tarski(sK3,k1_relat_1(sK1)) ),
% 47.81/6.49      inference(cnf_transformation,[],[f55]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_811,plain,
% 47.81/6.49      ( sK3 = sK3 ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_173]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_749,plain,
% 47.81/6.49      ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),k9_relat_1(X0,X1))
% 47.81/6.49      | r1_tarski(k9_relat_1(X0,X1),X2) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_1]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_824,plain,
% 47.81/6.49      ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
% 47.81/6.49      | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_749]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1401,plain,
% 47.81/6.49      ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
% 47.81/6.49      | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
% 47.81/6.49      | ~ r1_tarski(k9_relat_1(sK1,sK3),X0) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_2]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1594,plain,
% 47.81/6.49      ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,X0))
% 47.81/6.49      | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
% 47.81/6.49      | ~ r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,X0)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_1401]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_5,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1)
% 47.81/6.49      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 47.81/6.49      | ~ v1_relat_1(X2) ),
% 47.81/6.49      inference(cnf_transformation,[],[f42]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1595,plain,
% 47.81/6.49      ( r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,X0))
% 47.81/6.49      | ~ r1_tarski(sK3,X0)
% 47.81/6.49      | ~ v1_relat_1(sK1) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_5]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1971,plain,
% 47.81/6.49      ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_173]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_977,plain,
% 47.81/6.49      ( r2_hidden(sK0(sK3,X0),sK3) | r1_tarski(sK3,X0) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_1]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3040,plain,
% 47.81/6.49      ( r2_hidden(sK0(sK3,sK3),sK3) | r1_tarski(sK3,sK3) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_977]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_3041,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(sK3,sK3),sK3) | r1_tarski(sK3,sK3) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_0]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_989,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_175]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1987,plain,
% 47.81/6.49      ( ~ r1_tarski(sK3,X0) | r1_tarski(sK3,X1) | X1 != X0 | sK3 != sK3 ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_989]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_6983,plain,
% 47.81/6.49      ( r1_tarski(sK3,X0) | ~ r1_tarski(sK3,sK3) | X0 != sK3 | sK3 != sK3 ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_1987]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_852,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,X1)
% 47.81/6.49      | r1_tarski(X2,k1_relat_1(X3))
% 47.81/6.49      | X2 != X0
% 47.81/6.49      | k1_relat_1(X3) != X1 ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_175]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1093,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 47.81/6.49      | r1_tarski(X2,k1_relat_1(X1))
% 47.81/6.49      | X2 != X0
% 47.81/6.49      | k1_relat_1(X1) != k1_relat_1(X1) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_852]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_7190,plain,
% 47.81/6.49      ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | X0 != sK3
% 47.81/6.49      | k1_relat_1(k5_relat_1(sK1,sK2)) != k1_relat_1(k5_relat_1(sK1,sK2)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_1093]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_180,plain,
% 47.81/6.49      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 47.81/6.49      theory(equality) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_7381,plain,
% 47.81/6.49      ( k5_relat_1(sK1,sK2) != X0
% 47.81/6.49      | k1_relat_1(k5_relat_1(sK1,sK2)) = k1_relat_1(X0) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_180]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_18470,plain,
% 47.81/6.49      ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2)
% 47.81/6.49      | k1_relat_1(k5_relat_1(sK1,sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_7381]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_17484,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(X0,k1_relat_1(X1)),k1_relat_1(X1))
% 47.81/6.49      | r1_tarski(X0,k1_relat_1(X1)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_0]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_46121,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
% 47.81/6.49      | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_17484]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_513,plain,
% 47.81/6.49      ( r1_tarski(X0,X1) != iProver_top
% 47.81/6.49      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 47.81/6.49      | v1_relat_1(X2) != iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_7,plain,
% 47.81/6.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 47.81/6.49      | ~ v1_funct_1(X0)
% 47.81/6.49      | ~ v1_relat_1(X0) ),
% 47.81/6.49      inference(cnf_transformation,[],[f44]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_511,plain,
% 47.81/6.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 47.81/6.49      | v1_funct_1(X0) != iProver_top
% 47.81/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_517,plain,
% 47.81/6.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 47.81/6.49      | r1_tarski(X0,X1) = iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_516,plain,
% 47.81/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.81/6.49      | r2_hidden(X0,X2) = iProver_top
% 47.81/6.49      | r1_tarski(X1,X2) != iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_1932,plain,
% 47.81/6.49      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 47.81/6.49      | r1_tarski(X0,X2) != iProver_top
% 47.81/6.49      | r1_tarski(X0,X1) = iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_517,c_516]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_8974,plain,
% 47.81/6.49      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 47.81/6.49      | r1_tarski(X0,X3) != iProver_top
% 47.81/6.49      | r1_tarski(X3,X2) != iProver_top
% 47.81/6.49      | r1_tarski(X0,X1) = iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_1932,c_516]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_29260,plain,
% 47.81/6.49      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 47.81/6.49      | r1_tarski(X0,X1) = iProver_top
% 47.81/6.49      | r1_tarski(X0,k9_relat_1(X3,k10_relat_1(X3,X2))) != iProver_top
% 47.81/6.49      | v1_funct_1(X3) != iProver_top
% 47.81/6.49      | v1_relat_1(X3) != iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_511,c_8974]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_75100,plain,
% 47.81/6.49      ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),X3) = iProver_top
% 47.81/6.49      | r1_tarski(X1,k10_relat_1(X0,X3)) != iProver_top
% 47.81/6.49      | r1_tarski(k9_relat_1(X0,X1),X2) = iProver_top
% 47.81/6.49      | v1_funct_1(X0) != iProver_top
% 47.81/6.49      | v1_relat_1(X0) != iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_513,c_29260]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_518,plain,
% 47.81/6.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 47.81/6.49      | r1_tarski(X0,X1) = iProver_top ),
% 47.81/6.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_90453,plain,
% 47.81/6.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
% 47.81/6.49      | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
% 47.81/6.49      | v1_funct_1(X1) != iProver_top
% 47.81/6.49      | v1_relat_1(X1) != iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_75100,c_518]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_90747,plain,
% 47.81/6.49      ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
% 47.81/6.49      | r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(sK2)) = iProver_top
% 47.81/6.49      | v1_funct_1(sK1) != iProver_top
% 47.81/6.49      | v1_relat_1(sK1) != iProver_top ),
% 47.81/6.49      inference(superposition,[status(thm)],[c_2268,c_90453]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_91188,plain,
% 47.81/6.49      ( ~ r1_tarski(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
% 47.81/6.49      | r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(sK2))
% 47.81/6.49      | ~ v1_funct_1(sK1)
% 47.81/6.49      | ~ v1_relat_1(sK1) ),
% 47.81/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_90747]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_15286,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
% 47.81/6.49      | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X1)
% 47.81/6.49      | ~ r1_tarski(X0,X1) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_2]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_46120,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
% 47.81/6.49      | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
% 47.81/6.49      | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_15286]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_174330,plain,
% 47.81/6.49      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,X0))
% 47.81/6.49      | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
% 47.81/6.49      | ~ r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(sK2)) ),
% 47.81/6.49      inference(instantiation,[status(thm)],[c_46120]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_185889,plain,
% 47.81/6.49      ( X0 != sK3 ),
% 47.81/6.49      inference(global_propositional_subsumption,
% 47.81/6.49                [status(thm)],
% 47.81/6.49                [c_178894,c_18,c_17,c_16,c_15,c_14,c_12,c_703,c_811,c_824,
% 47.81/6.49                 c_986,c_1344,c_1529,c_1594,c_1595,c_1971,c_3040,c_3041,
% 47.81/6.49                 c_3266,c_6983,c_7190,c_18470,c_46121,c_91188,c_174330]) ).
% 47.81/6.49  
% 47.81/6.49  cnf(c_186731,plain,
% 47.81/6.49      ( $false ),
% 47.81/6.49      inference(resolution,[status(thm)],[c_185889,c_173]) ).
% 47.81/6.49  
% 47.81/6.49  
% 47.81/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.81/6.49  
% 47.81/6.49  ------                               Statistics
% 47.81/6.49  
% 47.81/6.49  ------ Selected
% 47.81/6.49  
% 47.81/6.49  total_time:                             5.717
% 47.81/6.49  
%------------------------------------------------------------------------------
