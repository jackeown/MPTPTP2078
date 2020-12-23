%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:30 EST 2020

% Result     : Theorem 19.50s
% Output     : CNFRefutation 19.50s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 558 expanded)
%              Number of clauses        :   68 ( 138 expanded)
%              Number of leaves         :   16 ( 151 expanded)
%              Depth                    :   20
%              Number of atoms          :  423 (3411 expanded)
%              Number of equality atoms :  218 (1740 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK5 != X1
        & k1_tarski(X0) = k2_relat_1(sK5)
        & k1_tarski(X0) = k2_relat_1(X1)
        & k1_relat_1(sK5) = k1_relat_1(X1)
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k1_tarski(X0) = k2_relat_1(X2)
            & k1_tarski(X0) = k2_relat_1(X1)
            & k1_relat_1(X1) = k1_relat_1(X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK4 != X2
          & k1_tarski(sK3) = k2_relat_1(X2)
          & k1_tarski(sK3) = k2_relat_1(sK4)
          & k1_relat_1(sK4) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK4 != sK5
    & k1_tarski(sK3) = k2_relat_1(sK5)
    & k1_tarski(sK3) = k2_relat_1(sK4)
    & k1_relat_1(sK4) = k1_relat_1(sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f37,f36])).

fof(f63,plain,(
    k1_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f34])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

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
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    k1_tarski(sK3) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f73,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK4) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f65,plain,(
    k1_tarski(sK3) = k2_relat_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK5) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( k1_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_754,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1219,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK4)
    | sK5 = X0
    | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_754])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3935,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_relat_1(sK4)
    | sK5 = X0
    | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1219,c_27,c_28])).

cnf(c_3936,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK4)
    | sK5 = X0
    | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3935])).

cnf(c_3943,plain,
    ( sK5 = sK4
    | r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3936])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_898,plain,
    ( r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_899,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK4 = sK5
    | r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_27898,plain,
    ( r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3943,c_25,c_26,c_27,c_28,c_20,c_17,c_899])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_756,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_750,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_760,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1493,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_750,c_760])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_762,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_236,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ v1_relat_1(X3)
    | X3 != X1
    | k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_237,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_749,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_19,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
    | X3 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_766,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1602,plain,
    ( sK3 = X0
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,k2_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_766])).

cnf(c_1719,plain,
    ( sK3 = X0
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_1602])).

cnf(c_4970,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1719,c_25])).

cnf(c_4971,plain,
    ( sK3 = X0
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4970])).

cnf(c_4974,plain,
    ( sK3 = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_762,c_4971])).

cnf(c_6078,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4974,c_25])).

cnf(c_6079,plain,
    ( sK3 = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6078])).

cnf(c_6085,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_6079])).

cnf(c_61219,plain,
    ( k1_funct_1(sK4,X0) = sK3
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_6085])).

cnf(c_61799,plain,
    ( k1_funct_1(sK4,X0) = sK3
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_61219,c_25,c_26])).

cnf(c_61808,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK5)) = sK3 ),
    inference(superposition,[status(thm)],[c_27898,c_61799])).

cnf(c_752,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1492,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_752,c_760])).

cnf(c_873,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK5))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_749])).

cnf(c_2850,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_27])).

cnf(c_2851,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK5))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2850])).

cnf(c_18,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1603,plain,
    ( sK3 = X0
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,k2_relat_1(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_766])).

cnf(c_2858,plain,
    ( sK3 = X0
    | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2851,c_1603])).

cnf(c_4368,plain,
    ( sK3 = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_762,c_2858])).

cnf(c_5395,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4368,c_27])).

cnf(c_5396,plain,
    ( sK3 = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5395])).

cnf(c_5402,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_5396])).

cnf(c_56930,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_5402])).

cnf(c_57261,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56930,c_27,c_28])).

cnf(c_57286,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_57261])).

cnf(c_57693,plain,
    ( k1_funct_1(sK5,sK2(sK4,sK5)) = sK3 ),
    inference(superposition,[status(thm)],[c_27898,c_57286])).

cnf(c_389,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_966,plain,
    ( k1_funct_1(sK5,sK2(sK4,sK5)) != X0
    | k1_funct_1(sK5,sK2(sK4,sK5)) = k1_funct_1(sK4,sK2(sK4,sK5))
    | k1_funct_1(sK4,sK2(sK4,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_967,plain,
    ( k1_funct_1(sK5,sK2(sK4,sK5)) = k1_funct_1(sK4,sK2(sK4,sK5))
    | k1_funct_1(sK5,sK2(sK4,sK5)) != sK3
    | k1_funct_1(sK4,sK2(sK4,sK5)) != sK3 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_901,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK5,sK2(sK4,sK5)) != k1_funct_1(sK4,sK2(sK4,sK5))
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61808,c_57693,c_967,c_901,c_17,c_20,c_21,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.50/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.50/2.98  
% 19.50/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.50/2.98  
% 19.50/2.98  ------  iProver source info
% 19.50/2.98  
% 19.50/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.50/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.50/2.98  git: non_committed_changes: false
% 19.50/2.98  git: last_make_outside_of_git: false
% 19.50/2.98  
% 19.50/2.98  ------ 
% 19.50/2.98  ------ Parsing...
% 19.50/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.50/2.98  
% 19.50/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.50/2.98  
% 19.50/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.50/2.98  
% 19.50/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.50/2.98  ------ Proving...
% 19.50/2.98  ------ Problem Properties 
% 19.50/2.98  
% 19.50/2.98  
% 19.50/2.98  clauses                                 24
% 19.50/2.98  conjectures                             8
% 19.50/2.98  EPR                                     5
% 19.50/2.98  Horn                                    23
% 19.50/2.98  unary                                   11
% 19.50/2.98  binary                                  5
% 19.50/2.98  lits                                    56
% 19.50/2.98  lits eq                                 13
% 19.50/2.98  fd_pure                                 0
% 19.50/2.98  fd_pseudo                               0
% 19.50/2.98  fd_cond                                 0
% 19.50/2.98  fd_pseudo_cond                          3
% 19.50/2.98  AC symbols                              0
% 19.50/2.98  
% 19.50/2.98  ------ Input Options Time Limit: Unbounded
% 19.50/2.98  
% 19.50/2.98  
% 19.50/2.98  ------ 
% 19.50/2.98  Current options:
% 19.50/2.98  ------ 
% 19.50/2.98  
% 19.50/2.98  
% 19.50/2.98  
% 19.50/2.98  
% 19.50/2.98  ------ Proving...
% 19.50/2.98  
% 19.50/2.98  
% 19.50/2.98  % SZS status Theorem for theBenchmark.p
% 19.50/2.98  
% 19.50/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.50/2.98  
% 19.50/2.98  fof(f12,conjecture,(
% 19.50/2.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f13,negated_conjecture,(
% 19.50/2.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 19.50/2.98    inference(negated_conjecture,[],[f12])).
% 19.50/2.98  
% 19.50/2.98  fof(f24,plain,(
% 19.50/2.98    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 19.50/2.98    inference(ennf_transformation,[],[f13])).
% 19.50/2.98  
% 19.50/2.98  fof(f25,plain,(
% 19.50/2.98    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 19.50/2.98    inference(flattening,[],[f24])).
% 19.50/2.98  
% 19.50/2.98  fof(f37,plain,(
% 19.50/2.98    ( ! [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK5 != X1 & k1_tarski(X0) = k2_relat_1(sK5) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(sK5) = k1_relat_1(X1) & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 19.50/2.98    introduced(choice_axiom,[])).
% 19.50/2.98  
% 19.50/2.98  fof(f36,plain,(
% 19.50/2.98    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK4 != X2 & k1_tarski(sK3) = k2_relat_1(X2) & k1_tarski(sK3) = k2_relat_1(sK4) & k1_relat_1(sK4) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 19.50/2.98    introduced(choice_axiom,[])).
% 19.50/2.98  
% 19.50/2.98  fof(f38,plain,(
% 19.50/2.98    (sK4 != sK5 & k1_tarski(sK3) = k2_relat_1(sK5) & k1_tarski(sK3) = k2_relat_1(sK4) & k1_relat_1(sK4) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 19.50/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f37,f36])).
% 19.50/2.98  
% 19.50/2.98  fof(f63,plain,(
% 19.50/2.98    k1_relat_1(sK4) = k1_relat_1(sK5)),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f11,axiom,(
% 19.50/2.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f22,plain,(
% 19.50/2.98    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.50/2.98    inference(ennf_transformation,[],[f11])).
% 19.50/2.98  
% 19.50/2.98  fof(f23,plain,(
% 19.50/2.98    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.50/2.98    inference(flattening,[],[f22])).
% 19.50/2.98  
% 19.50/2.98  fof(f34,plain,(
% 19.50/2.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 19.50/2.98    introduced(choice_axiom,[])).
% 19.50/2.98  
% 19.50/2.98  fof(f35,plain,(
% 19.50/2.98    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.50/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f34])).
% 19.50/2.98  
% 19.50/2.98  fof(f57,plain,(
% 19.50/2.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f35])).
% 19.50/2.98  
% 19.50/2.98  fof(f61,plain,(
% 19.50/2.98    v1_relat_1(sK5)),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f62,plain,(
% 19.50/2.98    v1_funct_1(sK5)),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f59,plain,(
% 19.50/2.98    v1_relat_1(sK4)),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f60,plain,(
% 19.50/2.98    v1_funct_1(sK4)),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f66,plain,(
% 19.50/2.98    sK4 != sK5),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f10,axiom,(
% 19.50/2.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f20,plain,(
% 19.50/2.98    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.50/2.98    inference(ennf_transformation,[],[f10])).
% 19.50/2.98  
% 19.50/2.98  fof(f21,plain,(
% 19.50/2.98    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.50/2.98    inference(flattening,[],[f20])).
% 19.50/2.98  
% 19.50/2.98  fof(f56,plain,(
% 19.50/2.98    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f21])).
% 19.50/2.98  
% 19.50/2.98  fof(f7,axiom,(
% 19.50/2.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f17,plain,(
% 19.50/2.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 19.50/2.98    inference(ennf_transformation,[],[f7])).
% 19.50/2.98  
% 19.50/2.98  fof(f50,plain,(
% 19.50/2.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f17])).
% 19.50/2.98  
% 19.50/2.98  fof(f6,axiom,(
% 19.50/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f16,plain,(
% 19.50/2.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 19.50/2.98    inference(ennf_transformation,[],[f6])).
% 19.50/2.98  
% 19.50/2.98  fof(f28,plain,(
% 19.50/2.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.50/2.98    inference(nnf_transformation,[],[f16])).
% 19.50/2.98  
% 19.50/2.98  fof(f29,plain,(
% 19.50/2.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.50/2.98    inference(rectify,[],[f28])).
% 19.50/2.98  
% 19.50/2.98  fof(f30,plain,(
% 19.50/2.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 19.50/2.98    introduced(choice_axiom,[])).
% 19.50/2.98  
% 19.50/2.98  fof(f31,plain,(
% 19.50/2.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.50/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 19.50/2.98  
% 19.50/2.98  fof(f47,plain,(
% 19.50/2.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f31])).
% 19.50/2.98  
% 19.50/2.98  fof(f1,axiom,(
% 19.50/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f14,plain,(
% 19.50/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.50/2.98    inference(unused_predicate_definition_removal,[],[f1])).
% 19.50/2.98  
% 19.50/2.98  fof(f15,plain,(
% 19.50/2.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 19.50/2.98    inference(ennf_transformation,[],[f14])).
% 19.50/2.98  
% 19.50/2.98  fof(f39,plain,(
% 19.50/2.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f15])).
% 19.50/2.98  
% 19.50/2.98  fof(f8,axiom,(
% 19.50/2.98    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f18,plain,(
% 19.50/2.98    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 19.50/2.98    inference(ennf_transformation,[],[f8])).
% 19.50/2.98  
% 19.50/2.98  fof(f51,plain,(
% 19.50/2.98    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f18])).
% 19.50/2.98  
% 19.50/2.98  fof(f64,plain,(
% 19.50/2.98    k1_tarski(sK3) = k2_relat_1(sK4)),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f2,axiom,(
% 19.50/2.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f40,plain,(
% 19.50/2.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f2])).
% 19.50/2.98  
% 19.50/2.98  fof(f3,axiom,(
% 19.50/2.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f41,plain,(
% 19.50/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f3])).
% 19.50/2.98  
% 19.50/2.98  fof(f4,axiom,(
% 19.50/2.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f42,plain,(
% 19.50/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f4])).
% 19.50/2.98  
% 19.50/2.98  fof(f67,plain,(
% 19.50/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.50/2.98    inference(definition_unfolding,[],[f41,f42])).
% 19.50/2.98  
% 19.50/2.98  fof(f68,plain,(
% 19.50/2.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.50/2.98    inference(definition_unfolding,[],[f40,f67])).
% 19.50/2.98  
% 19.50/2.98  fof(f73,plain,(
% 19.50/2.98    k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK4)),
% 19.50/2.98    inference(definition_unfolding,[],[f64,f68])).
% 19.50/2.98  
% 19.50/2.98  fof(f5,axiom,(
% 19.50/2.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 19.50/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.98  
% 19.50/2.98  fof(f26,plain,(
% 19.50/2.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 19.50/2.98    inference(nnf_transformation,[],[f5])).
% 19.50/2.98  
% 19.50/2.98  fof(f27,plain,(
% 19.50/2.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 19.50/2.98    inference(flattening,[],[f26])).
% 19.50/2.98  
% 19.50/2.98  fof(f44,plain,(
% 19.50/2.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 19.50/2.98    inference(cnf_transformation,[],[f27])).
% 19.50/2.98  
% 19.50/2.98  fof(f70,plain,(
% 19.50/2.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) )),
% 19.50/2.98    inference(definition_unfolding,[],[f44,f68])).
% 19.50/2.98  
% 19.50/2.98  fof(f65,plain,(
% 19.50/2.98    k1_tarski(sK3) = k2_relat_1(sK5)),
% 19.50/2.98    inference(cnf_transformation,[],[f38])).
% 19.50/2.98  
% 19.50/2.98  fof(f72,plain,(
% 19.50/2.98    k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK5)),
% 19.50/2.98    inference(definition_unfolding,[],[f65,f68])).
% 19.50/2.98  
% 19.50/2.98  fof(f58,plain,(
% 19.50/2.98    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.50/2.98    inference(cnf_transformation,[],[f35])).
% 19.50/2.98  
% 19.50/2.98  cnf(c_20,negated_conjecture,
% 19.50/2.98      ( k1_relat_1(sK4) = k1_relat_1(sK5) ),
% 19.50/2.98      inference(cnf_transformation,[],[f63]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_16,plain,
% 19.50/2.98      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 19.50/2.98      | ~ v1_funct_1(X1)
% 19.50/2.98      | ~ v1_funct_1(X0)
% 19.50/2.98      | ~ v1_relat_1(X1)
% 19.50/2.98      | ~ v1_relat_1(X0)
% 19.50/2.98      | X0 = X1
% 19.50/2.98      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 19.50/2.98      inference(cnf_transformation,[],[f57]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_754,plain,
% 19.50/2.98      ( X0 = X1
% 19.50/2.98      | k1_relat_1(X0) != k1_relat_1(X1)
% 19.50/2.98      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 19.50/2.98      | v1_funct_1(X1) != iProver_top
% 19.50/2.98      | v1_funct_1(X0) != iProver_top
% 19.50/2.98      | v1_relat_1(X1) != iProver_top
% 19.50/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_1219,plain,
% 19.50/2.98      ( k1_relat_1(X0) != k1_relat_1(sK4)
% 19.50/2.98      | sK5 = X0
% 19.50/2.98      | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
% 19.50/2.98      | v1_funct_1(X0) != iProver_top
% 19.50/2.98      | v1_funct_1(sK5) != iProver_top
% 19.50/2.98      | v1_relat_1(X0) != iProver_top
% 19.50/2.98      | v1_relat_1(sK5) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_20,c_754]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_22,negated_conjecture,
% 19.50/2.98      ( v1_relat_1(sK5) ),
% 19.50/2.98      inference(cnf_transformation,[],[f61]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_27,plain,
% 19.50/2.98      ( v1_relat_1(sK5) = iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_21,negated_conjecture,
% 19.50/2.98      ( v1_funct_1(sK5) ),
% 19.50/2.98      inference(cnf_transformation,[],[f62]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_28,plain,
% 19.50/2.98      ( v1_funct_1(sK5) = iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_3935,plain,
% 19.50/2.98      ( v1_relat_1(X0) != iProver_top
% 19.50/2.98      | k1_relat_1(X0) != k1_relat_1(sK4)
% 19.50/2.98      | sK5 = X0
% 19.50/2.98      | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
% 19.50/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_1219,c_27,c_28]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_3936,plain,
% 19.50/2.98      ( k1_relat_1(X0) != k1_relat_1(sK4)
% 19.50/2.98      | sK5 = X0
% 19.50/2.98      | r2_hidden(sK2(X0,sK5),k1_relat_1(X0)) = iProver_top
% 19.50/2.98      | v1_funct_1(X0) != iProver_top
% 19.50/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.50/2.98      inference(renaming,[status(thm)],[c_3935]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_3943,plain,
% 19.50/2.98      ( sK5 = sK4
% 19.50/2.98      | r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 19.50/2.98      | v1_funct_1(sK4) != iProver_top
% 19.50/2.98      | v1_relat_1(sK4) != iProver_top ),
% 19.50/2.98      inference(equality_resolution,[status(thm)],[c_3936]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_24,negated_conjecture,
% 19.50/2.98      ( v1_relat_1(sK4) ),
% 19.50/2.98      inference(cnf_transformation,[],[f59]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_25,plain,
% 19.50/2.98      ( v1_relat_1(sK4) = iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_23,negated_conjecture,
% 19.50/2.98      ( v1_funct_1(sK4) ),
% 19.50/2.98      inference(cnf_transformation,[],[f60]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_26,plain,
% 19.50/2.98      ( v1_funct_1(sK4) = iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_17,negated_conjecture,
% 19.50/2.98      ( sK4 != sK5 ),
% 19.50/2.98      inference(cnf_transformation,[],[f66]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_898,plain,
% 19.50/2.98      ( r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4))
% 19.50/2.98      | ~ v1_funct_1(sK5)
% 19.50/2.98      | ~ v1_funct_1(sK4)
% 19.50/2.98      | ~ v1_relat_1(sK5)
% 19.50/2.98      | ~ v1_relat_1(sK4)
% 19.50/2.98      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 19.50/2.98      | sK4 = sK5 ),
% 19.50/2.98      inference(instantiation,[status(thm)],[c_16]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_899,plain,
% 19.50/2.98      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 19.50/2.98      | sK4 = sK5
% 19.50/2.98      | r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 19.50/2.98      | v1_funct_1(sK5) != iProver_top
% 19.50/2.98      | v1_funct_1(sK4) != iProver_top
% 19.50/2.98      | v1_relat_1(sK5) != iProver_top
% 19.50/2.98      | v1_relat_1(sK4) != iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_27898,plain,
% 19.50/2.98      ( r2_hidden(sK2(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_3943,c_25,c_26,c_27,c_28,c_20,c_17,c_899]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_14,plain,
% 19.50/2.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.50/2.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 19.50/2.98      | ~ v1_funct_1(X1)
% 19.50/2.98      | ~ v1_relat_1(X1) ),
% 19.50/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_756,plain,
% 19.50/2.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 19.50/2.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 19.50/2.98      | v1_funct_1(X1) != iProver_top
% 19.50/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_750,plain,
% 19.50/2.98      ( v1_relat_1(sK4) = iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_8,plain,
% 19.50/2.98      ( ~ v1_relat_1(X0)
% 19.50/2.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 19.50/2.98      inference(cnf_transformation,[],[f50]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_760,plain,
% 19.50/2.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 19.50/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_1493,plain,
% 19.50/2.98      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_750,c_760]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_6,plain,
% 19.50/2.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.50/2.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 19.50/2.98      | ~ v1_relat_1(X1) ),
% 19.50/2.98      inference(cnf_transformation,[],[f47]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_762,plain,
% 19.50/2.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 19.50/2.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 19.50/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_0,plain,
% 19.50/2.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 19.50/2.98      inference(cnf_transformation,[],[f39]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_9,plain,
% 19.50/2.98      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 19.50/2.98      | ~ v1_relat_1(X0) ),
% 19.50/2.98      inference(cnf_transformation,[],[f51]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_236,plain,
% 19.50/2.98      ( ~ r2_hidden(X0,X1)
% 19.50/2.98      | r2_hidden(X0,X2)
% 19.50/2.98      | ~ v1_relat_1(X3)
% 19.50/2.98      | X3 != X1
% 19.50/2.98      | k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3)) != X2 ),
% 19.50/2.98      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_237,plain,
% 19.50/2.98      ( ~ r2_hidden(X0,X1)
% 19.50/2.98      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
% 19.50/2.98      | ~ v1_relat_1(X1) ),
% 19.50/2.98      inference(unflattening,[status(thm)],[c_236]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_749,plain,
% 19.50/2.98      ( r2_hidden(X0,X1) != iProver_top
% 19.50/2.98      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = iProver_top
% 19.50/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_19,negated_conjecture,
% 19.50/2.98      ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK4) ),
% 19.50/2.98      inference(cnf_transformation,[],[f73]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_2,plain,
% 19.50/2.98      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
% 19.50/2.98      | X3 = X1 ),
% 19.50/2.98      inference(cnf_transformation,[],[f70]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_766,plain,
% 19.50/2.98      ( X0 = X1
% 19.50/2.98      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_1602,plain,
% 19.50/2.98      ( sK3 = X0
% 19.50/2.98      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,k2_relat_1(sK4))) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_19,c_766]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_1719,plain,
% 19.50/2.98      ( sK3 = X0
% 19.50/2.98      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top
% 19.50/2.98      | v1_relat_1(sK4) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_749,c_1602]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_4970,plain,
% 19.50/2.98      ( r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top | sK3 = X0 ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_1719,c_25]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_4971,plain,
% 19.50/2.98      ( sK3 = X0 | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
% 19.50/2.98      inference(renaming,[status(thm)],[c_4970]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_4974,plain,
% 19.50/2.98      ( sK3 = X0
% 19.50/2.98      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 19.50/2.98      | v1_relat_1(sK4) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_762,c_4971]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_6078,plain,
% 19.50/2.98      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top | sK3 = X0 ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_4974,c_25]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_6079,plain,
% 19.50/2.98      ( sK3 = X0 | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 19.50/2.98      inference(renaming,[status(thm)],[c_6078]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_6085,plain,
% 19.50/2.98      ( sK3 = X0 | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_1493,c_6079]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_61219,plain,
% 19.50/2.98      ( k1_funct_1(sK4,X0) = sK3
% 19.50/2.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 19.50/2.98      | v1_funct_1(sK4) != iProver_top
% 19.50/2.98      | v1_relat_1(sK4) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_756,c_6085]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_61799,plain,
% 19.50/2.98      ( k1_funct_1(sK4,X0) = sK3
% 19.50/2.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_61219,c_25,c_26]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_61808,plain,
% 19.50/2.98      ( k1_funct_1(sK4,sK2(sK4,sK5)) = sK3 ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_27898,c_61799]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_752,plain,
% 19.50/2.98      ( v1_relat_1(sK5) = iProver_top ),
% 19.50/2.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_1492,plain,
% 19.50/2.98      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_752,c_760]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_873,plain,
% 19.50/2.98      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK5))) = iProver_top
% 19.50/2.98      | r2_hidden(X0,sK5) != iProver_top
% 19.50/2.98      | v1_relat_1(sK5) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_20,c_749]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_2850,plain,
% 19.50/2.98      ( r2_hidden(X0,sK5) != iProver_top
% 19.50/2.98      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK5))) = iProver_top ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_873,c_27]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_2851,plain,
% 19.50/2.98      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK5))) = iProver_top
% 19.50/2.98      | r2_hidden(X0,sK5) != iProver_top ),
% 19.50/2.98      inference(renaming,[status(thm)],[c_2850]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_18,negated_conjecture,
% 19.50/2.98      ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_relat_1(sK5) ),
% 19.50/2.98      inference(cnf_transformation,[],[f72]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_1603,plain,
% 19.50/2.98      ( sK3 = X0
% 19.50/2.98      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,k2_relat_1(sK5))) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_18,c_766]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_2858,plain,
% 19.50/2.98      ( sK3 = X0 | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_2851,c_1603]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_4368,plain,
% 19.50/2.98      ( sK3 = X0
% 19.50/2.98      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 19.50/2.98      | v1_relat_1(sK5) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_762,c_2858]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_5395,plain,
% 19.50/2.98      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top | sK3 = X0 ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_4368,c_27]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_5396,plain,
% 19.50/2.98      ( sK3 = X0 | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 19.50/2.98      inference(renaming,[status(thm)],[c_5395]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_5402,plain,
% 19.50/2.98      ( sK3 = X0 | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_1492,c_5396]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_56930,plain,
% 19.50/2.98      ( k1_funct_1(sK5,X0) = sK3
% 19.50/2.98      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 19.50/2.98      | v1_funct_1(sK5) != iProver_top
% 19.50/2.98      | v1_relat_1(sK5) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_756,c_5402]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_57261,plain,
% 19.50/2.98      ( k1_funct_1(sK5,X0) = sK3
% 19.50/2.98      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 19.50/2.98      inference(global_propositional_subsumption,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_56930,c_27,c_28]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_57286,plain,
% 19.50/2.98      ( k1_funct_1(sK5,X0) = sK3
% 19.50/2.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_20,c_57261]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_57693,plain,
% 19.50/2.98      ( k1_funct_1(sK5,sK2(sK4,sK5)) = sK3 ),
% 19.50/2.98      inference(superposition,[status(thm)],[c_27898,c_57286]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_389,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_966,plain,
% 19.50/2.98      ( k1_funct_1(sK5,sK2(sK4,sK5)) != X0
% 19.50/2.98      | k1_funct_1(sK5,sK2(sK4,sK5)) = k1_funct_1(sK4,sK2(sK4,sK5))
% 19.50/2.98      | k1_funct_1(sK4,sK2(sK4,sK5)) != X0 ),
% 19.50/2.98      inference(instantiation,[status(thm)],[c_389]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_967,plain,
% 19.50/2.98      ( k1_funct_1(sK5,sK2(sK4,sK5)) = k1_funct_1(sK4,sK2(sK4,sK5))
% 19.50/2.98      | k1_funct_1(sK5,sK2(sK4,sK5)) != sK3
% 19.50/2.98      | k1_funct_1(sK4,sK2(sK4,sK5)) != sK3 ),
% 19.50/2.98      inference(instantiation,[status(thm)],[c_966]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_15,plain,
% 19.50/2.98      ( ~ v1_funct_1(X0)
% 19.50/2.98      | ~ v1_funct_1(X1)
% 19.50/2.98      | ~ v1_relat_1(X0)
% 19.50/2.98      | ~ v1_relat_1(X1)
% 19.50/2.98      | X1 = X0
% 19.50/2.98      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 19.50/2.98      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 19.50/2.98      inference(cnf_transformation,[],[f58]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(c_901,plain,
% 19.50/2.98      ( ~ v1_funct_1(sK5)
% 19.50/2.98      | ~ v1_funct_1(sK4)
% 19.50/2.98      | ~ v1_relat_1(sK5)
% 19.50/2.98      | ~ v1_relat_1(sK4)
% 19.50/2.98      | k1_funct_1(sK5,sK2(sK4,sK5)) != k1_funct_1(sK4,sK2(sK4,sK5))
% 19.50/2.98      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 19.50/2.98      | sK4 = sK5 ),
% 19.50/2.98      inference(instantiation,[status(thm)],[c_15]) ).
% 19.50/2.98  
% 19.50/2.98  cnf(contradiction,plain,
% 19.50/2.98      ( $false ),
% 19.50/2.98      inference(minisat,
% 19.50/2.98                [status(thm)],
% 19.50/2.98                [c_61808,c_57693,c_967,c_901,c_17,c_20,c_21,c_22,c_23,
% 19.50/2.98                 c_24]) ).
% 19.50/2.98  
% 19.50/2.98  
% 19.50/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.50/2.98  
% 19.50/2.98  ------                               Statistics
% 19.50/2.98  
% 19.50/2.98  ------ Selected
% 19.50/2.98  
% 19.50/2.98  total_time:                             2.079
% 19.50/2.98  
%------------------------------------------------------------------------------
