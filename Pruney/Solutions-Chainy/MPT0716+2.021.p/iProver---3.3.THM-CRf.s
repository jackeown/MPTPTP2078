%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:55 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.71s
% Verified   : 
% Statistics : Number of formulae       :  151 (1878 expanded)
%              Number of clauses        :   95 ( 584 expanded)
%              Number of leaves         :   15 ( 447 expanded)
%              Depth                    :   26
%              Number of atoms          :  488 (12099 expanded)
%              Number of equality atoms :  165 ( 792 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
            | ~ r1_tarski(X2,k1_relat_1(X0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
          & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1))
          | ~ r1_tarski(sK2,k1_relat_1(X0))
          | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1))
            & r1_tarski(sK2,k1_relat_1(X0)) )
          | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))) ) )
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).

fof(f56,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_338,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_704,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_342,plain,
    ( ~ r1_tarski(X0_40,k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39)
    | k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_700,plain,
    ( k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40
    | r1_tarski(X0_40,k1_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_2059,plain,
    ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_700])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2771,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2059,c_21])).

cnf(c_2772,plain,
    ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2771])).

cnf(c_2778,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) = sK2
    | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
    | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2772,c_700])).

cnf(c_335,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_707,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_333,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_709,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_347,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_695,plain,
    ( k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39)
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_1812,plain,
    ( k7_relat_1(k5_relat_1(sK0,X0_39),X0_40) = k5_relat_1(k7_relat_1(sK0,X0_40),X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_695])).

cnf(c_2603,plain,
    ( k7_relat_1(k5_relat_1(sK0,sK1),X0_40) = k5_relat_1(k7_relat_1(sK0,X0_40),sK1) ),
    inference(superposition,[status(thm)],[c_707,c_1812])).

cnf(c_2790,plain,
    ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
    | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
    | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2778,c_2603])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_349,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1049,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_2804,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
    | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2790])).

cnf(c_43942,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
    | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2790,c_18,c_16,c_1049,c_2804])).

cnf(c_43943,plain,
    ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
    | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
    inference(renaming,[status(thm)],[c_43942])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_343,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_39,X0_40)),k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_699,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_39,X0_40)),k1_relat_1(X0_39)) = iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_43953,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
    | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_43943,c_699])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_348,plain,
    ( ~ v1_relat_1(X0_39)
    | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_378,plain,
    ( v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_337,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_705,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_350,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X2_40,X0_40)
    | r1_tarski(X2_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_692,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(X2_40,X0_40) != iProver_top
    | r1_tarski(X2_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_1013,plain,
    ( r1_tarski(X0_40,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0_40,sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_692])).

cnf(c_19,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_23,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_864,plain,
    ( r1_tarski(X0_40,k1_relat_1(X0_39))
    | ~ r1_tarski(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39)))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_958,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_959,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_345,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1001,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1002,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_1422,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_19,c_21,c_23,c_959,c_1002])).

cnf(c_1424,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1422])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_346,plain,
    ( ~ v1_relat_1(X0_39)
    | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_696,plain,
    ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1090,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0_40)) = k9_relat_1(sK0,X0_40) ),
    inference(superposition,[status(thm)],[c_709,c_696])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_344,plain,
    ( ~ r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_698,plain,
    ( k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39)
    | r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_2274,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0_40),X0_39)) = k1_relat_1(k7_relat_1(sK0,X0_40))
    | r1_tarski(k9_relat_1(sK0,X0_40),k1_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k7_relat_1(sK0,X0_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_698])).

cnf(c_35036,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = k1_relat_1(k7_relat_1(sK0,sK2))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_2274])).

cnf(c_2060,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_700])).

cnf(c_393,plain,
    ( k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40
    | r1_tarski(X0_40,k1_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_395,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_3253,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2060,c_19,c_21,c_23,c_395,c_959,c_1002])).

cnf(c_35207,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35036,c_3253])).

cnf(c_35264,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_35207])).

cnf(c_44046,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_43953])).

cnf(c_44334,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43953,c_18,c_16,c_12,c_378,c_1424,c_35264,c_44046])).

cnf(c_11,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_340,plain,
    ( r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39))
    | ~ v1_funct_1(X1_39)
    | ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | k1_relat_1(k5_relat_1(X0_39,X1_39)) != k1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_702,plain,
    ( k1_relat_1(k5_relat_1(X0_39,X1_39)) != k1_relat_1(X0_39)
    | r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39)) = iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_44340,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != sK2
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_44334,c_702])).

cnf(c_44406,plain,
    ( sK2 != sK2
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_44340,c_3253])).

cnf(c_44407,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_44406])).

cnf(c_44408,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_44407,c_1090])).

cnf(c_2631,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0_40),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_699])).

cnf(c_1050,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_7335,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0_40),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2631,c_19,c_21,c_1050])).

cnf(c_44347,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_44334,c_7335])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_341,plain,
    ( ~ v1_funct_1(X0_39)
    | v1_funct_1(k7_relat_1(X0_39,X0_40))
    | ~ v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_396,plain,
    ( v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(k7_relat_1(X0_39,X0_40)) = iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_398,plain,
    ( v1_funct_1(k7_relat_1(sK0,sK2)) = iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_377,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k7_relat_1(X0_39,X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_379,plain,
    ( v1_relat_1(k7_relat_1(sK0,sK2)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_25,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44408,c_44347,c_1422,c_398,c_379,c_25,c_22,c_21,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.71/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.71/1.99  
% 11.71/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.71/1.99  
% 11.71/1.99  ------  iProver source info
% 11.71/1.99  
% 11.71/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.71/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.71/1.99  git: non_committed_changes: false
% 11.71/1.99  git: last_make_outside_of_git: false
% 11.71/1.99  
% 11.71/1.99  ------ 
% 11.71/1.99  
% 11.71/1.99  ------ Input Options
% 11.71/1.99  
% 11.71/1.99  --out_options                           all
% 11.71/1.99  --tptp_safe_out                         true
% 11.71/1.99  --problem_path                          ""
% 11.71/1.99  --include_path                          ""
% 11.71/1.99  --clausifier                            res/vclausify_rel
% 11.71/1.99  --clausifier_options                    --mode clausify
% 11.71/1.99  --stdin                                 false
% 11.71/1.99  --stats_out                             all
% 11.71/1.99  
% 11.71/1.99  ------ General Options
% 11.71/1.99  
% 11.71/1.99  --fof                                   false
% 11.71/1.99  --time_out_real                         305.
% 11.71/1.99  --time_out_virtual                      -1.
% 11.71/1.99  --symbol_type_check                     false
% 11.71/1.99  --clausify_out                          false
% 11.71/1.99  --sig_cnt_out                           false
% 11.71/1.99  --trig_cnt_out                          false
% 11.71/1.99  --trig_cnt_out_tolerance                1.
% 11.71/1.99  --trig_cnt_out_sk_spl                   false
% 11.71/1.99  --abstr_cl_out                          false
% 11.71/1.99  
% 11.71/1.99  ------ Global Options
% 11.71/1.99  
% 11.71/1.99  --schedule                              default
% 11.71/1.99  --add_important_lit                     false
% 11.71/1.99  --prop_solver_per_cl                    1000
% 11.71/1.99  --min_unsat_core                        false
% 11.71/1.99  --soft_assumptions                      false
% 11.71/1.99  --soft_lemma_size                       3
% 11.71/1.99  --prop_impl_unit_size                   0
% 11.71/1.99  --prop_impl_unit                        []
% 11.71/1.99  --share_sel_clauses                     true
% 11.71/1.99  --reset_solvers                         false
% 11.71/1.99  --bc_imp_inh                            [conj_cone]
% 11.71/1.99  --conj_cone_tolerance                   3.
% 11.71/1.99  --extra_neg_conj                        none
% 11.71/1.99  --large_theory_mode                     true
% 11.71/1.99  --prolific_symb_bound                   200
% 11.71/1.99  --lt_threshold                          2000
% 11.71/1.99  --clause_weak_htbl                      true
% 11.71/1.99  --gc_record_bc_elim                     false
% 11.71/1.99  
% 11.71/1.99  ------ Preprocessing Options
% 11.71/1.99  
% 11.71/1.99  --preprocessing_flag                    true
% 11.71/1.99  --time_out_prep_mult                    0.1
% 11.71/1.99  --splitting_mode                        input
% 11.71/1.99  --splitting_grd                         true
% 11.71/1.99  --splitting_cvd                         false
% 11.71/1.99  --splitting_cvd_svl                     false
% 11.71/1.99  --splitting_nvd                         32
% 11.71/1.99  --sub_typing                            true
% 11.71/1.99  --prep_gs_sim                           true
% 11.71/1.99  --prep_unflatten                        true
% 11.71/1.99  --prep_res_sim                          true
% 11.71/1.99  --prep_upred                            true
% 11.71/1.99  --prep_sem_filter                       exhaustive
% 11.71/1.99  --prep_sem_filter_out                   false
% 11.71/1.99  --pred_elim                             true
% 11.71/1.99  --res_sim_input                         true
% 11.71/1.99  --eq_ax_congr_red                       true
% 11.71/1.99  --pure_diseq_elim                       true
% 11.71/1.99  --brand_transform                       false
% 11.71/1.99  --non_eq_to_eq                          false
% 11.71/1.99  --prep_def_merge                        true
% 11.71/1.99  --prep_def_merge_prop_impl              false
% 11.71/1.99  --prep_def_merge_mbd                    true
% 11.71/1.99  --prep_def_merge_tr_red                 false
% 11.71/1.99  --prep_def_merge_tr_cl                  false
% 11.71/1.99  --smt_preprocessing                     true
% 11.71/1.99  --smt_ac_axioms                         fast
% 11.71/1.99  --preprocessed_out                      false
% 11.71/1.99  --preprocessed_stats                    false
% 11.71/1.99  
% 11.71/1.99  ------ Abstraction refinement Options
% 11.71/1.99  
% 11.71/1.99  --abstr_ref                             []
% 11.71/1.99  --abstr_ref_prep                        false
% 11.71/1.99  --abstr_ref_until_sat                   false
% 11.71/1.99  --abstr_ref_sig_restrict                funpre
% 11.71/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.71/1.99  --abstr_ref_under                       []
% 11.71/1.99  
% 11.71/1.99  ------ SAT Options
% 11.71/1.99  
% 11.71/1.99  --sat_mode                              false
% 11.71/1.99  --sat_fm_restart_options                ""
% 11.71/1.99  --sat_gr_def                            false
% 11.71/1.99  --sat_epr_types                         true
% 11.71/1.99  --sat_non_cyclic_types                  false
% 11.71/1.99  --sat_finite_models                     false
% 11.71/1.99  --sat_fm_lemmas                         false
% 11.71/1.99  --sat_fm_prep                           false
% 11.71/1.99  --sat_fm_uc_incr                        true
% 11.71/1.99  --sat_out_model                         small
% 11.71/1.99  --sat_out_clauses                       false
% 11.71/1.99  
% 11.71/1.99  ------ QBF Options
% 11.71/1.99  
% 11.71/1.99  --qbf_mode                              false
% 11.71/1.99  --qbf_elim_univ                         false
% 11.71/1.99  --qbf_dom_inst                          none
% 11.71/1.99  --qbf_dom_pre_inst                      false
% 11.71/1.99  --qbf_sk_in                             false
% 11.71/1.99  --qbf_pred_elim                         true
% 11.71/1.99  --qbf_split                             512
% 11.71/1.99  
% 11.71/1.99  ------ BMC1 Options
% 11.71/1.99  
% 11.71/1.99  --bmc1_incremental                      false
% 11.71/1.99  --bmc1_axioms                           reachable_all
% 11.71/1.99  --bmc1_min_bound                        0
% 11.71/1.99  --bmc1_max_bound                        -1
% 11.71/1.99  --bmc1_max_bound_default                -1
% 11.71/1.99  --bmc1_symbol_reachability              true
% 11.71/1.99  --bmc1_property_lemmas                  false
% 11.71/1.99  --bmc1_k_induction                      false
% 11.71/1.99  --bmc1_non_equiv_states                 false
% 11.71/1.99  --bmc1_deadlock                         false
% 11.71/1.99  --bmc1_ucm                              false
% 11.71/1.99  --bmc1_add_unsat_core                   none
% 11.71/1.99  --bmc1_unsat_core_children              false
% 11.71/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.71/1.99  --bmc1_out_stat                         full
% 11.71/1.99  --bmc1_ground_init                      false
% 11.71/1.99  --bmc1_pre_inst_next_state              false
% 11.71/1.99  --bmc1_pre_inst_state                   false
% 11.71/1.99  --bmc1_pre_inst_reach_state             false
% 11.71/1.99  --bmc1_out_unsat_core                   false
% 11.71/1.99  --bmc1_aig_witness_out                  false
% 11.71/1.99  --bmc1_verbose                          false
% 11.71/1.99  --bmc1_dump_clauses_tptp                false
% 11.71/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.71/1.99  --bmc1_dump_file                        -
% 11.71/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.71/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.71/1.99  --bmc1_ucm_extend_mode                  1
% 11.71/1.99  --bmc1_ucm_init_mode                    2
% 11.71/1.99  --bmc1_ucm_cone_mode                    none
% 11.71/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.71/1.99  --bmc1_ucm_relax_model                  4
% 11.71/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.71/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.71/1.99  --bmc1_ucm_layered_model                none
% 11.71/1.99  --bmc1_ucm_max_lemma_size               10
% 11.71/1.99  
% 11.71/1.99  ------ AIG Options
% 11.71/1.99  
% 11.71/1.99  --aig_mode                              false
% 11.71/1.99  
% 11.71/1.99  ------ Instantiation Options
% 11.71/1.99  
% 11.71/1.99  --instantiation_flag                    true
% 11.71/1.99  --inst_sos_flag                         false
% 11.71/1.99  --inst_sos_phase                        true
% 11.71/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.71/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.71/1.99  --inst_lit_sel_side                     num_symb
% 11.71/1.99  --inst_solver_per_active                1400
% 11.71/1.99  --inst_solver_calls_frac                1.
% 11.71/1.99  --inst_passive_queue_type               priority_queues
% 11.71/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.71/1.99  --inst_passive_queues_freq              [25;2]
% 11.71/1.99  --inst_dismatching                      true
% 11.71/1.99  --inst_eager_unprocessed_to_passive     true
% 11.71/1.99  --inst_prop_sim_given                   true
% 11.71/1.99  --inst_prop_sim_new                     false
% 11.71/1.99  --inst_subs_new                         false
% 11.71/1.99  --inst_eq_res_simp                      false
% 11.71/1.99  --inst_subs_given                       false
% 11.71/1.99  --inst_orphan_elimination               true
% 11.71/1.99  --inst_learning_loop_flag               true
% 11.71/1.99  --inst_learning_start                   3000
% 11.71/1.99  --inst_learning_factor                  2
% 11.71/1.99  --inst_start_prop_sim_after_learn       3
% 11.71/1.99  --inst_sel_renew                        solver
% 11.71/1.99  --inst_lit_activity_flag                true
% 11.71/1.99  --inst_restr_to_given                   false
% 11.71/1.99  --inst_activity_threshold               500
% 11.71/1.99  --inst_out_proof                        true
% 11.71/1.99  
% 11.71/1.99  ------ Resolution Options
% 11.71/1.99  
% 11.71/1.99  --resolution_flag                       true
% 11.71/1.99  --res_lit_sel                           adaptive
% 11.71/1.99  --res_lit_sel_side                      none
% 11.71/1.99  --res_ordering                          kbo
% 11.71/1.99  --res_to_prop_solver                    active
% 11.71/1.99  --res_prop_simpl_new                    false
% 11.71/1.99  --res_prop_simpl_given                  true
% 11.71/1.99  --res_passive_queue_type                priority_queues
% 11.71/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.71/1.99  --res_passive_queues_freq               [15;5]
% 11.71/1.99  --res_forward_subs                      full
% 11.71/1.99  --res_backward_subs                     full
% 11.71/1.99  --res_forward_subs_resolution           true
% 11.71/1.99  --res_backward_subs_resolution          true
% 11.71/1.99  --res_orphan_elimination                true
% 11.71/1.99  --res_time_limit                        2.
% 11.71/1.99  --res_out_proof                         true
% 11.71/1.99  
% 11.71/1.99  ------ Superposition Options
% 11.71/1.99  
% 11.71/1.99  --superposition_flag                    true
% 11.71/1.99  --sup_passive_queue_type                priority_queues
% 11.71/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.71/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.71/1.99  --demod_completeness_check              fast
% 11.71/1.99  --demod_use_ground                      true
% 11.71/1.99  --sup_to_prop_solver                    passive
% 11.71/1.99  --sup_prop_simpl_new                    true
% 11.71/1.99  --sup_prop_simpl_given                  true
% 11.71/1.99  --sup_fun_splitting                     false
% 11.71/1.99  --sup_smt_interval                      50000
% 11.71/1.99  
% 11.71/1.99  ------ Superposition Simplification Setup
% 11.71/1.99  
% 11.71/1.99  --sup_indices_passive                   []
% 11.71/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.71/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.99  --sup_full_bw                           [BwDemod]
% 11.71/1.99  --sup_immed_triv                        [TrivRules]
% 11.71/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.99  --sup_immed_bw_main                     []
% 11.71/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.71/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/1.99  
% 11.71/1.99  ------ Combination Options
% 11.71/1.99  
% 11.71/1.99  --comb_res_mult                         3
% 11.71/1.99  --comb_sup_mult                         2
% 11.71/1.99  --comb_inst_mult                        10
% 11.71/1.99  
% 11.71/1.99  ------ Debug Options
% 11.71/1.99  
% 11.71/1.99  --dbg_backtrace                         false
% 11.71/1.99  --dbg_dump_prop_clauses                 false
% 11.71/1.99  --dbg_dump_prop_clauses_file            -
% 11.71/1.99  --dbg_out_stat                          false
% 11.71/1.99  ------ Parsing...
% 11.71/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.71/1.99  
% 11.71/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.71/1.99  
% 11.71/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.71/1.99  
% 11.71/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.71/1.99  ------ Proving...
% 11.71/1.99  ------ Problem Properties 
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  clauses                                 18
% 11.71/1.99  conjectures                             7
% 11.71/1.99  EPR                                     5
% 11.71/1.99  Horn                                    16
% 11.71/1.99  unary                                   4
% 11.71/1.99  binary                                  5
% 11.71/1.99  lits                                    45
% 11.71/1.99  lits eq                                 5
% 11.71/1.99  fd_pure                                 0
% 11.71/1.99  fd_pseudo                               0
% 11.71/1.99  fd_cond                                 0
% 11.71/1.99  fd_pseudo_cond                          0
% 11.71/1.99  AC symbols                              0
% 11.71/1.99  
% 11.71/1.99  ------ Schedule dynamic 5 is on 
% 11.71/1.99  
% 11.71/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  ------ 
% 11.71/1.99  Current options:
% 11.71/1.99  ------ 
% 11.71/1.99  
% 11.71/1.99  ------ Input Options
% 11.71/1.99  
% 11.71/1.99  --out_options                           all
% 11.71/1.99  --tptp_safe_out                         true
% 11.71/1.99  --problem_path                          ""
% 11.71/1.99  --include_path                          ""
% 11.71/1.99  --clausifier                            res/vclausify_rel
% 11.71/1.99  --clausifier_options                    --mode clausify
% 11.71/1.99  --stdin                                 false
% 11.71/1.99  --stats_out                             all
% 11.71/1.99  
% 11.71/1.99  ------ General Options
% 11.71/1.99  
% 11.71/1.99  --fof                                   false
% 11.71/1.99  --time_out_real                         305.
% 11.71/1.99  --time_out_virtual                      -1.
% 11.71/1.99  --symbol_type_check                     false
% 11.71/1.99  --clausify_out                          false
% 11.71/1.99  --sig_cnt_out                           false
% 11.71/1.99  --trig_cnt_out                          false
% 11.71/1.99  --trig_cnt_out_tolerance                1.
% 11.71/1.99  --trig_cnt_out_sk_spl                   false
% 11.71/1.99  --abstr_cl_out                          false
% 11.71/1.99  
% 11.71/1.99  ------ Global Options
% 11.71/1.99  
% 11.71/1.99  --schedule                              default
% 11.71/1.99  --add_important_lit                     false
% 11.71/1.99  --prop_solver_per_cl                    1000
% 11.71/1.99  --min_unsat_core                        false
% 11.71/1.99  --soft_assumptions                      false
% 11.71/1.99  --soft_lemma_size                       3
% 11.71/1.99  --prop_impl_unit_size                   0
% 11.71/1.99  --prop_impl_unit                        []
% 11.71/1.99  --share_sel_clauses                     true
% 11.71/1.99  --reset_solvers                         false
% 11.71/1.99  --bc_imp_inh                            [conj_cone]
% 11.71/1.99  --conj_cone_tolerance                   3.
% 11.71/1.99  --extra_neg_conj                        none
% 11.71/1.99  --large_theory_mode                     true
% 11.71/1.99  --prolific_symb_bound                   200
% 11.71/1.99  --lt_threshold                          2000
% 11.71/1.99  --clause_weak_htbl                      true
% 11.71/1.99  --gc_record_bc_elim                     false
% 11.71/1.99  
% 11.71/1.99  ------ Preprocessing Options
% 11.71/1.99  
% 11.71/1.99  --preprocessing_flag                    true
% 11.71/1.99  --time_out_prep_mult                    0.1
% 11.71/1.99  --splitting_mode                        input
% 11.71/1.99  --splitting_grd                         true
% 11.71/1.99  --splitting_cvd                         false
% 11.71/1.99  --splitting_cvd_svl                     false
% 11.71/1.99  --splitting_nvd                         32
% 11.71/1.99  --sub_typing                            true
% 11.71/1.99  --prep_gs_sim                           true
% 11.71/1.99  --prep_unflatten                        true
% 11.71/1.99  --prep_res_sim                          true
% 11.71/1.99  --prep_upred                            true
% 11.71/1.99  --prep_sem_filter                       exhaustive
% 11.71/1.99  --prep_sem_filter_out                   false
% 11.71/1.99  --pred_elim                             true
% 11.71/1.99  --res_sim_input                         true
% 11.71/1.99  --eq_ax_congr_red                       true
% 11.71/1.99  --pure_diseq_elim                       true
% 11.71/1.99  --brand_transform                       false
% 11.71/1.99  --non_eq_to_eq                          false
% 11.71/1.99  --prep_def_merge                        true
% 11.71/1.99  --prep_def_merge_prop_impl              false
% 11.71/1.99  --prep_def_merge_mbd                    true
% 11.71/1.99  --prep_def_merge_tr_red                 false
% 11.71/1.99  --prep_def_merge_tr_cl                  false
% 11.71/1.99  --smt_preprocessing                     true
% 11.71/1.99  --smt_ac_axioms                         fast
% 11.71/1.99  --preprocessed_out                      false
% 11.71/1.99  --preprocessed_stats                    false
% 11.71/1.99  
% 11.71/1.99  ------ Abstraction refinement Options
% 11.71/1.99  
% 11.71/1.99  --abstr_ref                             []
% 11.71/1.99  --abstr_ref_prep                        false
% 11.71/1.99  --abstr_ref_until_sat                   false
% 11.71/1.99  --abstr_ref_sig_restrict                funpre
% 11.71/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.71/1.99  --abstr_ref_under                       []
% 11.71/1.99  
% 11.71/1.99  ------ SAT Options
% 11.71/1.99  
% 11.71/1.99  --sat_mode                              false
% 11.71/1.99  --sat_fm_restart_options                ""
% 11.71/1.99  --sat_gr_def                            false
% 11.71/1.99  --sat_epr_types                         true
% 11.71/1.99  --sat_non_cyclic_types                  false
% 11.71/1.99  --sat_finite_models                     false
% 11.71/1.99  --sat_fm_lemmas                         false
% 11.71/1.99  --sat_fm_prep                           false
% 11.71/1.99  --sat_fm_uc_incr                        true
% 11.71/1.99  --sat_out_model                         small
% 11.71/1.99  --sat_out_clauses                       false
% 11.71/1.99  
% 11.71/1.99  ------ QBF Options
% 11.71/1.99  
% 11.71/1.99  --qbf_mode                              false
% 11.71/1.99  --qbf_elim_univ                         false
% 11.71/1.99  --qbf_dom_inst                          none
% 11.71/1.99  --qbf_dom_pre_inst                      false
% 11.71/1.99  --qbf_sk_in                             false
% 11.71/1.99  --qbf_pred_elim                         true
% 11.71/1.99  --qbf_split                             512
% 11.71/1.99  
% 11.71/1.99  ------ BMC1 Options
% 11.71/1.99  
% 11.71/1.99  --bmc1_incremental                      false
% 11.71/1.99  --bmc1_axioms                           reachable_all
% 11.71/1.99  --bmc1_min_bound                        0
% 11.71/1.99  --bmc1_max_bound                        -1
% 11.71/1.99  --bmc1_max_bound_default                -1
% 11.71/1.99  --bmc1_symbol_reachability              true
% 11.71/1.99  --bmc1_property_lemmas                  false
% 11.71/1.99  --bmc1_k_induction                      false
% 11.71/1.99  --bmc1_non_equiv_states                 false
% 11.71/1.99  --bmc1_deadlock                         false
% 11.71/1.99  --bmc1_ucm                              false
% 11.71/1.99  --bmc1_add_unsat_core                   none
% 11.71/1.99  --bmc1_unsat_core_children              false
% 11.71/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.71/1.99  --bmc1_out_stat                         full
% 11.71/1.99  --bmc1_ground_init                      false
% 11.71/1.99  --bmc1_pre_inst_next_state              false
% 11.71/1.99  --bmc1_pre_inst_state                   false
% 11.71/1.99  --bmc1_pre_inst_reach_state             false
% 11.71/1.99  --bmc1_out_unsat_core                   false
% 11.71/1.99  --bmc1_aig_witness_out                  false
% 11.71/1.99  --bmc1_verbose                          false
% 11.71/1.99  --bmc1_dump_clauses_tptp                false
% 11.71/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.71/1.99  --bmc1_dump_file                        -
% 11.71/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.71/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.71/1.99  --bmc1_ucm_extend_mode                  1
% 11.71/1.99  --bmc1_ucm_init_mode                    2
% 11.71/1.99  --bmc1_ucm_cone_mode                    none
% 11.71/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.71/1.99  --bmc1_ucm_relax_model                  4
% 11.71/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.71/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.71/1.99  --bmc1_ucm_layered_model                none
% 11.71/1.99  --bmc1_ucm_max_lemma_size               10
% 11.71/1.99  
% 11.71/1.99  ------ AIG Options
% 11.71/1.99  
% 11.71/1.99  --aig_mode                              false
% 11.71/1.99  
% 11.71/1.99  ------ Instantiation Options
% 11.71/1.99  
% 11.71/1.99  --instantiation_flag                    true
% 11.71/1.99  --inst_sos_flag                         false
% 11.71/1.99  --inst_sos_phase                        true
% 11.71/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.71/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.71/1.99  --inst_lit_sel_side                     none
% 11.71/1.99  --inst_solver_per_active                1400
% 11.71/1.99  --inst_solver_calls_frac                1.
% 11.71/1.99  --inst_passive_queue_type               priority_queues
% 11.71/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.71/1.99  --inst_passive_queues_freq              [25;2]
% 11.71/1.99  --inst_dismatching                      true
% 11.71/1.99  --inst_eager_unprocessed_to_passive     true
% 11.71/1.99  --inst_prop_sim_given                   true
% 11.71/1.99  --inst_prop_sim_new                     false
% 11.71/1.99  --inst_subs_new                         false
% 11.71/1.99  --inst_eq_res_simp                      false
% 11.71/1.99  --inst_subs_given                       false
% 11.71/1.99  --inst_orphan_elimination               true
% 11.71/1.99  --inst_learning_loop_flag               true
% 11.71/1.99  --inst_learning_start                   3000
% 11.71/1.99  --inst_learning_factor                  2
% 11.71/1.99  --inst_start_prop_sim_after_learn       3
% 11.71/1.99  --inst_sel_renew                        solver
% 11.71/1.99  --inst_lit_activity_flag                true
% 11.71/1.99  --inst_restr_to_given                   false
% 11.71/1.99  --inst_activity_threshold               500
% 11.71/1.99  --inst_out_proof                        true
% 11.71/1.99  
% 11.71/1.99  ------ Resolution Options
% 11.71/1.99  
% 11.71/1.99  --resolution_flag                       false
% 11.71/1.99  --res_lit_sel                           adaptive
% 11.71/1.99  --res_lit_sel_side                      none
% 11.71/1.99  --res_ordering                          kbo
% 11.71/1.99  --res_to_prop_solver                    active
% 11.71/1.99  --res_prop_simpl_new                    false
% 11.71/1.99  --res_prop_simpl_given                  true
% 11.71/1.99  --res_passive_queue_type                priority_queues
% 11.71/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.71/1.99  --res_passive_queues_freq               [15;5]
% 11.71/1.99  --res_forward_subs                      full
% 11.71/1.99  --res_backward_subs                     full
% 11.71/1.99  --res_forward_subs_resolution           true
% 11.71/1.99  --res_backward_subs_resolution          true
% 11.71/1.99  --res_orphan_elimination                true
% 11.71/1.99  --res_time_limit                        2.
% 11.71/1.99  --res_out_proof                         true
% 11.71/1.99  
% 11.71/1.99  ------ Superposition Options
% 11.71/1.99  
% 11.71/1.99  --superposition_flag                    true
% 11.71/1.99  --sup_passive_queue_type                priority_queues
% 11.71/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.71/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.71/1.99  --demod_completeness_check              fast
% 11.71/1.99  --demod_use_ground                      true
% 11.71/1.99  --sup_to_prop_solver                    passive
% 11.71/1.99  --sup_prop_simpl_new                    true
% 11.71/1.99  --sup_prop_simpl_given                  true
% 11.71/1.99  --sup_fun_splitting                     false
% 11.71/1.99  --sup_smt_interval                      50000
% 11.71/1.99  
% 11.71/1.99  ------ Superposition Simplification Setup
% 11.71/1.99  
% 11.71/1.99  --sup_indices_passive                   []
% 11.71/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.71/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.99  --sup_full_bw                           [BwDemod]
% 11.71/1.99  --sup_immed_triv                        [TrivRules]
% 11.71/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.99  --sup_immed_bw_main                     []
% 11.71/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.71/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/1.99  
% 11.71/1.99  ------ Combination Options
% 11.71/1.99  
% 11.71/1.99  --comb_res_mult                         3
% 11.71/1.99  --comb_sup_mult                         2
% 11.71/1.99  --comb_inst_mult                        10
% 11.71/1.99  
% 11.71/1.99  ------ Debug Options
% 11.71/1.99  
% 11.71/1.99  --dbg_backtrace                         false
% 11.71/1.99  --dbg_dump_prop_clauses                 false
% 11.71/1.99  --dbg_dump_prop_clauses_file            -
% 11.71/1.99  --dbg_out_stat                          false
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  ------ Proving...
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  % SZS status Theorem for theBenchmark.p
% 11.71/1.99  
% 11.71/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.71/1.99  
% 11.71/1.99  fof(f12,conjecture,(
% 11.71/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f13,negated_conjecture,(
% 11.71/1.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 11.71/1.99    inference(negated_conjecture,[],[f12])).
% 11.71/1.99  
% 11.71/1.99  fof(f31,plain,(
% 11.71/1.99    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 11.71/1.99    inference(ennf_transformation,[],[f13])).
% 11.71/1.99  
% 11.71/1.99  fof(f32,plain,(
% 11.71/1.99    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.71/1.99    inference(flattening,[],[f31])).
% 11.71/1.99  
% 11.71/1.99  fof(f33,plain,(
% 11.71/1.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.71/1.99    inference(nnf_transformation,[],[f32])).
% 11.71/1.99  
% 11.71/1.99  fof(f34,plain,(
% 11.71/1.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.71/1.99    inference(flattening,[],[f33])).
% 11.71/1.99  
% 11.71/1.99  fof(f37,plain,(
% 11.71/1.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) | ~r1_tarski(sK2,k1_relat_1(X0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) & r1_tarski(sK2,k1_relat_1(X0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 11.71/1.99    introduced(choice_axiom,[])).
% 11.71/1.99  
% 11.71/1.99  fof(f36,plain,(
% 11.71/1.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 11.71/1.99    introduced(choice_axiom,[])).
% 11.71/1.99  
% 11.71/1.99  fof(f35,plain,(
% 11.71/1.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 11.71/1.99    introduced(choice_axiom,[])).
% 11.71/1.99  
% 11.71/1.99  fof(f38,plain,(
% 11.71/1.99    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 11.71/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).
% 11.71/1.99  
% 11.71/1.99  fof(f56,plain,(
% 11.71/1.99    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.71/1.99    inference(cnf_transformation,[],[f38])).
% 11.71/1.99  
% 11.71/1.99  fof(f9,axiom,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f25,plain,(
% 11.71/1.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.71/1.99    inference(ennf_transformation,[],[f9])).
% 11.71/1.99  
% 11.71/1.99  fof(f26,plain,(
% 11.71/1.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.71/1.99    inference(flattening,[],[f25])).
% 11.71/1.99  
% 11.71/1.99  fof(f47,plain,(
% 11.71/1.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f26])).
% 11.71/1.99  
% 11.71/1.99  fof(f53,plain,(
% 11.71/1.99    v1_relat_1(sK1)),
% 11.71/1.99    inference(cnf_transformation,[],[f38])).
% 11.71/1.99  
% 11.71/1.99  fof(f51,plain,(
% 11.71/1.99    v1_relat_1(sK0)),
% 11.71/1.99    inference(cnf_transformation,[],[f38])).
% 11.71/1.99  
% 11.71/1.99  fof(f4,axiom,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f19,plain,(
% 11.71/1.99    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 11.71/1.99    inference(ennf_transformation,[],[f4])).
% 11.71/1.99  
% 11.71/1.99  fof(f42,plain,(
% 11.71/1.99    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f19])).
% 11.71/1.99  
% 11.71/1.99  fof(f2,axiom,(
% 11.71/1.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f16,plain,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 11.71/1.99    inference(ennf_transformation,[],[f2])).
% 11.71/1.99  
% 11.71/1.99  fof(f17,plain,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 11.71/1.99    inference(flattening,[],[f16])).
% 11.71/1.99  
% 11.71/1.99  fof(f40,plain,(
% 11.71/1.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f17])).
% 11.71/1.99  
% 11.71/1.99  fof(f8,axiom,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f24,plain,(
% 11.71/1.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.71/1.99    inference(ennf_transformation,[],[f8])).
% 11.71/1.99  
% 11.71/1.99  fof(f46,plain,(
% 11.71/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f24])).
% 11.71/1.99  
% 11.71/1.99  fof(f57,plain,(
% 11.71/1.99    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.71/1.99    inference(cnf_transformation,[],[f38])).
% 11.71/1.99  
% 11.71/1.99  fof(f3,axiom,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f18,plain,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.71/1.99    inference(ennf_transformation,[],[f3])).
% 11.71/1.99  
% 11.71/1.99  fof(f41,plain,(
% 11.71/1.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f18])).
% 11.71/1.99  
% 11.71/1.99  fof(f55,plain,(
% 11.71/1.99    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.71/1.99    inference(cnf_transformation,[],[f38])).
% 11.71/1.99  
% 11.71/1.99  fof(f1,axiom,(
% 11.71/1.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f14,plain,(
% 11.71/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.71/1.99    inference(ennf_transformation,[],[f1])).
% 11.71/1.99  
% 11.71/1.99  fof(f15,plain,(
% 11.71/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.71/1.99    inference(flattening,[],[f14])).
% 11.71/1.99  
% 11.71/1.99  fof(f39,plain,(
% 11.71/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f15])).
% 11.71/1.99  
% 11.71/1.99  fof(f6,axiom,(
% 11.71/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f21,plain,(
% 11.71/1.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.71/1.99    inference(ennf_transformation,[],[f6])).
% 11.71/1.99  
% 11.71/1.99  fof(f44,plain,(
% 11.71/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f21])).
% 11.71/1.99  
% 11.71/1.99  fof(f5,axiom,(
% 11.71/1.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f20,plain,(
% 11.71/1.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.71/1.99    inference(ennf_transformation,[],[f5])).
% 11.71/1.99  
% 11.71/1.99  fof(f43,plain,(
% 11.71/1.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f20])).
% 11.71/1.99  
% 11.71/1.99  fof(f7,axiom,(
% 11.71/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f22,plain,(
% 11.71/1.99    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.71/1.99    inference(ennf_transformation,[],[f7])).
% 11.71/1.99  
% 11.71/1.99  fof(f23,plain,(
% 11.71/1.99    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.71/1.99    inference(flattening,[],[f22])).
% 11.71/1.99  
% 11.71/1.99  fof(f45,plain,(
% 11.71/1.99    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f23])).
% 11.71/1.99  
% 11.71/1.99  fof(f11,axiom,(
% 11.71/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f29,plain,(
% 11.71/1.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.71/1.99    inference(ennf_transformation,[],[f11])).
% 11.71/1.99  
% 11.71/1.99  fof(f30,plain,(
% 11.71/1.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.71/1.99    inference(flattening,[],[f29])).
% 11.71/1.99  
% 11.71/1.99  fof(f50,plain,(
% 11.71/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f30])).
% 11.71/1.99  
% 11.71/1.99  fof(f10,axiom,(
% 11.71/1.99    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 11.71/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.71/1.99  
% 11.71/1.99  fof(f27,plain,(
% 11.71/1.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.71/1.99    inference(ennf_transformation,[],[f10])).
% 11.71/1.99  
% 11.71/1.99  fof(f28,plain,(
% 11.71/1.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.71/1.99    inference(flattening,[],[f27])).
% 11.71/1.99  
% 11.71/1.99  fof(f49,plain,(
% 11.71/1.99    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.71/1.99    inference(cnf_transformation,[],[f28])).
% 11.71/1.99  
% 11.71/1.99  fof(f54,plain,(
% 11.71/1.99    v1_funct_1(sK1)),
% 11.71/1.99    inference(cnf_transformation,[],[f38])).
% 11.71/1.99  
% 11.71/1.99  fof(f52,plain,(
% 11.71/1.99    v1_funct_1(sK0)),
% 11.71/1.99    inference(cnf_transformation,[],[f38])).
% 11.71/1.99  
% 11.71/1.99  cnf(c_13,negated_conjecture,
% 11.71/1.99      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 11.71/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_338,negated_conjecture,
% 11.71/1.99      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_13]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_704,plain,
% 11.71/1.99      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_8,plain,
% 11.71/1.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.71/1.99      | ~ v1_relat_1(X1)
% 11.71/1.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 11.71/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_342,plain,
% 11.71/1.99      ( ~ r1_tarski(X0_40,k1_relat_1(X0_39))
% 11.71/1.99      | ~ v1_relat_1(X0_39)
% 11.71/1.99      | k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40 ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_700,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40
% 11.71/1.99      | r1_tarski(X0_40,k1_relat_1(X0_39)) != iProver_top
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2059,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_704,c_700]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_16,negated_conjecture,
% 11.71/1.99      ( v1_relat_1(sK1) ),
% 11.71/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_21,plain,
% 11.71/1.99      ( v1_relat_1(sK1) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2771,plain,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2) ),
% 11.71/1.99      inference(global_propositional_subsumption,
% 11.71/1.99                [status(thm)],
% 11.71/1.99                [c_2059,c_21]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2772,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.71/1.99      inference(renaming,[status(thm)],[c_2771]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2778,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) = sK2
% 11.71/1.99      | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
% 11.71/1.99      | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_2772,c_700]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_335,negated_conjecture,
% 11.71/1.99      ( v1_relat_1(sK1) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_16]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_707,plain,
% 11.71/1.99      ( v1_relat_1(sK1) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_18,negated_conjecture,
% 11.71/1.99      ( v1_relat_1(sK0) ),
% 11.71/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_333,negated_conjecture,
% 11.71/1.99      ( v1_relat_1(sK0) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_18]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_709,plain,
% 11.71/1.99      ( v1_relat_1(sK0) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_3,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0)
% 11.71/1.99      | ~ v1_relat_1(X1)
% 11.71/1.99      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 11.71/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_347,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0_39)
% 11.71/1.99      | ~ v1_relat_1(X1_39)
% 11.71/1.99      | k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_695,plain,
% 11.71/1.99      ( k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39)
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top
% 11.71/1.99      | v1_relat_1(X1_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1812,plain,
% 11.71/1.99      ( k7_relat_1(k5_relat_1(sK0,X0_39),X0_40) = k5_relat_1(k7_relat_1(sK0,X0_40),X0_39)
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_709,c_695]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2603,plain,
% 11.71/1.99      ( k7_relat_1(k5_relat_1(sK0,sK1),X0_40) = k5_relat_1(k7_relat_1(sK0,X0_40),sK1) ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_707,c_1812]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2790,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
% 11.71/1.99      | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
% 11.71/1.99      | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
% 11.71/1.99      inference(demodulation,[status(thm)],[c_2778,c_2603]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0)
% 11.71/1.99      | ~ v1_relat_1(X1)
% 11.71/1.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 11.71/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_349,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0_39)
% 11.71/1.99      | ~ v1_relat_1(X1_39)
% 11.71/1.99      | v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1049,plain,
% 11.71/1.99      ( v1_relat_1(k5_relat_1(sK0,sK1))
% 11.71/1.99      | ~ v1_relat_1(sK1)
% 11.71/1.99      | ~ v1_relat_1(sK0) ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_349]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2804,plain,
% 11.71/1.99      ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
% 11.71/1.99      | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
% 11.71/1.99      | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
% 11.71/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2790]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_43942,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
% 11.71/1.99      | k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2) ),
% 11.71/1.99      inference(global_propositional_subsumption,
% 11.71/1.99                [status(thm)],
% 11.71/1.99                [c_2790,c_18,c_16,c_1049,c_2804]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_43943,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK1,k9_relat_1(sK0,sK2))) = k9_relat_1(sK0,sK2)
% 11.71/1.99      | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
% 11.71/1.99      inference(renaming,[status(thm)],[c_43942]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_7,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 11.71/1.99      | ~ v1_relat_1(X0) ),
% 11.71/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_343,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_39,X0_40)),k1_relat_1(X0_39))
% 11.71/1.99      | ~ v1_relat_1(X0_39) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_7]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_699,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_39,X0_40)),k1_relat_1(X0_39)) = iProver_top
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_43953,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
% 11.71/1.99      | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_43943,c_699]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_12,negated_conjecture,
% 11.71/1.99      ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.71/1.99      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.71/1.99      | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.71/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.71/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_348,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0_39) | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_378,plain,
% 11.71/1.99      ( v1_relat_1(k7_relat_1(sK0,sK2)) | ~ v1_relat_1(sK0) ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_348]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_14,negated_conjecture,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.71/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_337,negated_conjecture,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_14]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_705,plain,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_0,plain,
% 11.71/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 11.71/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_350,plain,
% 11.71/1.99      ( ~ r1_tarski(X0_40,X1_40)
% 11.71/1.99      | ~ r1_tarski(X2_40,X0_40)
% 11.71/1.99      | r1_tarski(X2_40,X1_40) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_0]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_692,plain,
% 11.71/1.99      ( r1_tarski(X0_40,X1_40) != iProver_top
% 11.71/1.99      | r1_tarski(X2_40,X0_40) != iProver_top
% 11.71/1.99      | r1_tarski(X2_40,X1_40) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1013,plain,
% 11.71/1.99      ( r1_tarski(X0_40,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | r1_tarski(X0_40,sK2) != iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_705,c_692]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_19,plain,
% 11.71/1.99      ( v1_relat_1(sK0) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_23,plain,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_864,plain,
% 11.71/1.99      ( r1_tarski(X0_40,k1_relat_1(X0_39))
% 11.71/1.99      | ~ r1_tarski(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39)))
% 11.71/1.99      | ~ r1_tarski(k1_relat_1(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_350]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_958,plain,
% 11.71/1.99      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
% 11.71/1.99      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_864]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_959,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) != iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_5,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 11.71/1.99      | ~ v1_relat_1(X1)
% 11.71/1.99      | ~ v1_relat_1(X0) ),
% 11.71/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_345,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39))
% 11.71/1.99      | ~ v1_relat_1(X0_39)
% 11.71/1.99      | ~ v1_relat_1(X1_39) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_5]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1001,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
% 11.71/1.99      | ~ v1_relat_1(sK1)
% 11.71/1.99      | ~ v1_relat_1(sK0) ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_345]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1002,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top
% 11.71/1.99      | v1_relat_1(sK0) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1422,plain,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.71/1.99      inference(global_propositional_subsumption,
% 11.71/1.99                [status(thm)],
% 11.71/1.99                [c_1013,c_19,c_21,c_23,c_959,c_1002]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1424,plain,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.71/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_1422]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_4,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0)
% 11.71/1.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.71/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_346,plain,
% 11.71/1.99      ( ~ v1_relat_1(X0_39)
% 11.71/1.99      | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_4]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_696,plain,
% 11.71/1.99      ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1090,plain,
% 11.71/1.99      ( k2_relat_1(k7_relat_1(sK0,X0_40)) = k9_relat_1(sK0,X0_40) ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_709,c_696]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_6,plain,
% 11.71/1.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 11.71/1.99      | ~ v1_relat_1(X1)
% 11.71/1.99      | ~ v1_relat_1(X0)
% 11.71/1.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 11.71/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_344,plain,
% 11.71/1.99      ( ~ r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39))
% 11.71/1.99      | ~ v1_relat_1(X0_39)
% 11.71/1.99      | ~ v1_relat_1(X1_39)
% 11.71/1.99      | k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_6]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_698,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39)
% 11.71/1.99      | r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39)) != iProver_top
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top
% 11.71/1.99      | v1_relat_1(X1_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2274,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0_40),X0_39)) = k1_relat_1(k7_relat_1(sK0,X0_40))
% 11.71/1.99      | r1_tarski(k9_relat_1(sK0,X0_40),k1_relat_1(X0_39)) != iProver_top
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(sK0,X0_40)) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_1090,c_698]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_35036,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = k1_relat_1(k7_relat_1(sK0,sK2))
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_704,c_2274]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2060,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2
% 11.71/1.99      | v1_relat_1(sK0) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_1422,c_700]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_393,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40
% 11.71/1.99      | r1_tarski(X0_40,k1_relat_1(X0_39)) != iProver_top
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_395,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
% 11.71/1.99      | v1_relat_1(sK0) != iProver_top ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_393]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_3253,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2 ),
% 11.71/1.99      inference(global_propositional_subsumption,
% 11.71/1.99                [status(thm)],
% 11.71/1.99                [c_2060,c_19,c_21,c_23,c_395,c_959,c_1002]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_35207,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(light_normalisation,[status(thm)],[c_35036,c_3253]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_35264,plain,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.71/1.99      | ~ v1_relat_1(k7_relat_1(sK0,sK2))
% 11.71/1.99      | ~ v1_relat_1(sK1)
% 11.71/1.99      | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
% 11.71/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_35207]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_44046,plain,
% 11.71/1.99      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.71/1.99      | ~ v1_relat_1(sK1)
% 11.71/1.99      | k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
% 11.71/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_43953]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_44334,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
% 11.71/1.99      inference(global_propositional_subsumption,
% 11.71/1.99                [status(thm)],
% 11.71/1.99                [c_43953,c_18,c_16,c_12,c_378,c_1424,c_35264,c_44046]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_11,plain,
% 11.71/1.99      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 11.71/1.99      | ~ v1_funct_1(X1)
% 11.71/1.99      | ~ v1_funct_1(X0)
% 11.71/1.99      | ~ v1_relat_1(X0)
% 11.71/1.99      | ~ v1_relat_1(X1)
% 11.71/1.99      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 11.71/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_340,plain,
% 11.71/1.99      ( r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39))
% 11.71/1.99      | ~ v1_funct_1(X1_39)
% 11.71/1.99      | ~ v1_funct_1(X0_39)
% 11.71/1.99      | ~ v1_relat_1(X0_39)
% 11.71/1.99      | ~ v1_relat_1(X1_39)
% 11.71/1.99      | k1_relat_1(k5_relat_1(X0_39,X1_39)) != k1_relat_1(X0_39) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_11]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_702,plain,
% 11.71/1.99      ( k1_relat_1(k5_relat_1(X0_39,X1_39)) != k1_relat_1(X0_39)
% 11.71/1.99      | r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39)) = iProver_top
% 11.71/1.99      | v1_funct_1(X1_39) != iProver_top
% 11.71/1.99      | v1_funct_1(X0_39) != iProver_top
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top
% 11.71/1.99      | v1_relat_1(X1_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_44340,plain,
% 11.71/1.99      ( k1_relat_1(k7_relat_1(sK0,sK2)) != sK2
% 11.71/1.99      | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
% 11.71/1.99      | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_funct_1(sK1) != iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_44334,c_702]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_44406,plain,
% 11.71/1.99      ( sK2 != sK2
% 11.71/1.99      | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
% 11.71/1.99      | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_funct_1(sK1) != iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(light_normalisation,[status(thm)],[c_44340,c_3253]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_44407,plain,
% 11.71/1.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
% 11.71/1.99      | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_funct_1(sK1) != iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(equality_resolution_simp,[status(thm)],[c_44406]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_44408,plain,
% 11.71/1.99      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 11.71/1.99      | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_funct_1(sK1) != iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.71/1.99      inference(demodulation,[status(thm)],[c_44407,c_1090]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_2631,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0_40),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.71/1.99      | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_2603,c_699]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_1050,plain,
% 11.71/1.99      ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
% 11.71/1.99      | v1_relat_1(sK1) != iProver_top
% 11.71/1.99      | v1_relat_1(sK0) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_1049]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_7335,plain,
% 11.71/1.99      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0_40),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.71/1.99      inference(global_propositional_subsumption,
% 11.71/1.99                [status(thm)],
% 11.71/1.99                [c_2631,c_19,c_21,c_1050]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_44347,plain,
% 11.71/1.99      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.71/1.99      inference(superposition,[status(thm)],[c_44334,c_7335]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_9,plain,
% 11.71/1.99      ( ~ v1_funct_1(X0)
% 11.71/1.99      | v1_funct_1(k7_relat_1(X0,X1))
% 11.71/1.99      | ~ v1_relat_1(X0) ),
% 11.71/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_341,plain,
% 11.71/1.99      ( ~ v1_funct_1(X0_39)
% 11.71/1.99      | v1_funct_1(k7_relat_1(X0_39,X0_40))
% 11.71/1.99      | ~ v1_relat_1(X0_39) ),
% 11.71/1.99      inference(subtyping,[status(esa)],[c_9]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_396,plain,
% 11.71/1.99      ( v1_funct_1(X0_39) != iProver_top
% 11.71/1.99      | v1_funct_1(k7_relat_1(X0_39,X0_40)) = iProver_top
% 11.71/1.99      | v1_relat_1(X0_39) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_398,plain,
% 11.71/1.99      ( v1_funct_1(k7_relat_1(sK0,sK2)) = iProver_top
% 11.71/1.99      | v1_funct_1(sK0) != iProver_top
% 11.71/1.99      | v1_relat_1(sK0) != iProver_top ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_396]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_377,plain,
% 11.71/1.99      ( v1_relat_1(X0_39) != iProver_top
% 11.71/1.99      | v1_relat_1(k7_relat_1(X0_39,X0_40)) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_379,plain,
% 11.71/1.99      ( v1_relat_1(k7_relat_1(sK0,sK2)) = iProver_top
% 11.71/1.99      | v1_relat_1(sK0) != iProver_top ),
% 11.71/1.99      inference(instantiation,[status(thm)],[c_377]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_25,plain,
% 11.71/1.99      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 11.71/1.99      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_15,negated_conjecture,
% 11.71/1.99      ( v1_funct_1(sK1) ),
% 11.71/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_22,plain,
% 11.71/1.99      ( v1_funct_1(sK1) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_17,negated_conjecture,
% 11.71/1.99      ( v1_funct_1(sK0) ),
% 11.71/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(c_20,plain,
% 11.71/1.99      ( v1_funct_1(sK0) = iProver_top ),
% 11.71/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.71/1.99  
% 11.71/1.99  cnf(contradiction,plain,
% 11.71/1.99      ( $false ),
% 11.71/1.99      inference(minisat,
% 11.71/1.99                [status(thm)],
% 11.71/1.99                [c_44408,c_44347,c_1422,c_398,c_379,c_25,c_22,c_21,c_20,
% 11.71/1.99                 c_19]) ).
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.71/1.99  
% 11.71/1.99  ------                               Statistics
% 11.71/1.99  
% 11.71/1.99  ------ General
% 11.71/1.99  
% 11.71/1.99  abstr_ref_over_cycles:                  0
% 11.71/1.99  abstr_ref_under_cycles:                 0
% 11.71/1.99  gc_basic_clause_elim:                   0
% 11.71/1.99  forced_gc_time:                         0
% 11.71/1.99  parsing_time:                           0.008
% 11.71/1.99  unif_index_cands_time:                  0.
% 11.71/1.99  unif_index_add_time:                    0.
% 11.71/1.99  orderings_time:                         0.
% 11.71/1.99  out_proof_time:                         0.015
% 11.71/1.99  total_time:                             1.14
% 11.71/1.99  num_of_symbols:                         44
% 11.71/1.99  num_of_terms:                           48337
% 11.71/1.99  
% 11.71/1.99  ------ Preprocessing
% 11.71/1.99  
% 11.71/1.99  num_of_splits:                          0
% 11.71/1.99  num_of_split_atoms:                     0
% 11.71/1.99  num_of_reused_defs:                     0
% 11.71/1.99  num_eq_ax_congr_red:                    3
% 11.71/1.99  num_of_sem_filtered_clauses:            1
% 11.71/1.99  num_of_subtypes:                        2
% 11.71/1.99  monotx_restored_types:                  1
% 11.71/1.99  sat_num_of_epr_types:                   0
% 11.71/1.99  sat_num_of_non_cyclic_types:            0
% 11.71/1.99  sat_guarded_non_collapsed_types:        0
% 11.71/1.99  num_pure_diseq_elim:                    0
% 11.71/1.99  simp_replaced_by:                       0
% 11.71/1.99  res_preprocessed:                       97
% 11.71/1.99  prep_upred:                             0
% 11.71/1.99  prep_unflattend:                        0
% 11.71/1.99  smt_new_axioms:                         0
% 11.71/1.99  pred_elim_cands:                        3
% 11.71/1.99  pred_elim:                              0
% 11.71/1.99  pred_elim_cl:                           0
% 11.71/1.99  pred_elim_cycles:                       2
% 11.71/1.99  merged_defs:                            0
% 11.71/1.99  merged_defs_ncl:                        0
% 11.71/1.99  bin_hyper_res:                          0
% 11.71/1.99  prep_cycles:                            4
% 11.71/1.99  pred_elim_time:                         0.
% 11.71/1.99  splitting_time:                         0.
% 11.71/1.99  sem_filter_time:                        0.
% 11.71/1.99  monotx_time:                            0.
% 11.71/1.99  subtype_inf_time:                       0.001
% 11.71/1.99  
% 11.71/1.99  ------ Problem properties
% 11.71/1.99  
% 11.71/1.99  clauses:                                18
% 11.71/1.99  conjectures:                            7
% 11.71/1.99  epr:                                    5
% 11.71/1.99  horn:                                   16
% 11.71/1.99  ground:                                 7
% 11.71/1.99  unary:                                  4
% 11.71/1.99  binary:                                 5
% 11.71/1.99  lits:                                   45
% 11.71/1.99  lits_eq:                                5
% 11.71/1.99  fd_pure:                                0
% 11.71/1.99  fd_pseudo:                              0
% 11.71/1.99  fd_cond:                                0
% 11.71/1.99  fd_pseudo_cond:                         0
% 11.71/1.99  ac_symbols:                             0
% 11.71/1.99  
% 11.71/1.99  ------ Propositional Solver
% 11.71/1.99  
% 11.71/1.99  prop_solver_calls:                      32
% 11.71/1.99  prop_fast_solver_calls:                 980
% 11.71/1.99  smt_solver_calls:                       0
% 11.71/1.99  smt_fast_solver_calls:                  0
% 11.71/1.99  prop_num_of_clauses:                    13384
% 11.71/1.99  prop_preprocess_simplified:             17963
% 11.71/1.99  prop_fo_subsumed:                       41
% 11.71/1.99  prop_solver_time:                       0.
% 11.71/1.99  smt_solver_time:                        0.
% 11.71/1.99  smt_fast_solver_time:                   0.
% 11.71/1.99  prop_fast_solver_time:                  0.
% 11.71/1.99  prop_unsat_core_time:                   0.001
% 11.71/1.99  
% 11.71/1.99  ------ QBF
% 11.71/1.99  
% 11.71/1.99  qbf_q_res:                              0
% 11.71/1.99  qbf_num_tautologies:                    0
% 11.71/1.99  qbf_prep_cycles:                        0
% 11.71/1.99  
% 11.71/1.99  ------ BMC1
% 11.71/1.99  
% 11.71/1.99  bmc1_current_bound:                     -1
% 11.71/1.99  bmc1_last_solved_bound:                 -1
% 11.71/1.99  bmc1_unsat_core_size:                   -1
% 11.71/1.99  bmc1_unsat_core_parents_size:           -1
% 11.71/1.99  bmc1_merge_next_fun:                    0
% 11.71/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.71/1.99  
% 11.71/1.99  ------ Instantiation
% 11.71/1.99  
% 11.71/1.99  inst_num_of_clauses:                    2238
% 11.71/1.99  inst_num_in_passive:                    1186
% 11.71/1.99  inst_num_in_active:                     966
% 11.71/1.99  inst_num_in_unprocessed:                86
% 11.71/1.99  inst_num_of_loops:                      1190
% 11.71/1.99  inst_num_of_learning_restarts:          0
% 11.71/1.99  inst_num_moves_active_passive:          220
% 11.71/1.99  inst_lit_activity:                      0
% 11.71/1.99  inst_lit_activity_moves:                0
% 11.71/1.99  inst_num_tautologies:                   0
% 11.71/1.99  inst_num_prop_implied:                  0
% 11.71/1.99  inst_num_existing_simplified:           0
% 11.71/1.99  inst_num_eq_res_simplified:             0
% 11.71/1.99  inst_num_child_elim:                    0
% 11.71/1.99  inst_num_of_dismatching_blockings:      9810
% 11.71/1.99  inst_num_of_non_proper_insts:           4334
% 11.71/1.99  inst_num_of_duplicates:                 0
% 11.71/1.99  inst_inst_num_from_inst_to_res:         0
% 11.71/1.99  inst_dismatching_checking_time:         0.
% 11.71/1.99  
% 11.71/1.99  ------ Resolution
% 11.71/1.99  
% 11.71/1.99  res_num_of_clauses:                     0
% 11.71/1.99  res_num_in_passive:                     0
% 11.71/1.99  res_num_in_active:                      0
% 11.71/1.99  res_num_of_loops:                       101
% 11.71/1.99  res_forward_subset_subsumed:            52
% 11.71/1.99  res_backward_subset_subsumed:           0
% 11.71/1.99  res_forward_subsumed:                   0
% 11.71/1.99  res_backward_subsumed:                  0
% 11.71/1.99  res_forward_subsumption_resolution:     0
% 11.71/1.99  res_backward_subsumption_resolution:    0
% 11.71/1.99  res_clause_to_clause_subsumption:       4567
% 11.71/1.99  res_orphan_elimination:                 0
% 11.71/1.99  res_tautology_del:                      402
% 11.71/1.99  res_num_eq_res_simplified:              0
% 11.71/1.99  res_num_sel_changes:                    0
% 11.71/1.99  res_moves_from_active_to_pass:          0
% 11.71/1.99  
% 11.71/1.99  ------ Superposition
% 11.71/1.99  
% 11.71/1.99  sup_time_total:                         0.
% 11.71/1.99  sup_time_generating:                    0.
% 11.71/1.99  sup_time_sim_full:                      0.
% 11.71/1.99  sup_time_sim_immed:                     0.
% 11.71/1.99  
% 11.71/1.99  sup_num_of_clauses:                     1688
% 11.71/1.99  sup_num_in_active:                      234
% 11.71/1.99  sup_num_in_passive:                     1454
% 11.71/1.99  sup_num_of_loops:                       236
% 11.71/1.99  sup_fw_superposition:                   716
% 11.71/1.99  sup_bw_superposition:                   1064
% 11.71/1.99  sup_immediate_simplified:               147
% 11.71/1.99  sup_given_eliminated:                   0
% 11.71/1.99  comparisons_done:                       0
% 11.71/1.99  comparisons_avoided:                    3
% 11.71/1.99  
% 11.71/1.99  ------ Simplifications
% 11.71/1.99  
% 11.71/1.99  
% 11.71/1.99  sim_fw_subset_subsumed:                 46
% 11.71/1.99  sim_bw_subset_subsumed:                 28
% 11.71/1.99  sim_fw_subsumed:                        17
% 11.71/1.99  sim_bw_subsumed:                        0
% 11.71/1.99  sim_fw_subsumption_res:                 0
% 11.71/1.99  sim_bw_subsumption_res:                 0
% 11.71/1.99  sim_tautology_del:                      3
% 11.71/1.99  sim_eq_tautology_del:                   0
% 11.71/1.99  sim_eq_res_simp:                        1
% 11.71/1.99  sim_fw_demodulated:                     15
% 11.71/1.99  sim_bw_demodulated:                     2
% 11.71/1.99  sim_light_normalised:                   70
% 11.71/1.99  sim_joinable_taut:                      0
% 11.71/1.99  sim_joinable_simp:                      0
% 11.71/1.99  sim_ac_normalised:                      0
% 11.71/1.99  sim_smt_subsumption:                    0
% 11.71/1.99  
%------------------------------------------------------------------------------
