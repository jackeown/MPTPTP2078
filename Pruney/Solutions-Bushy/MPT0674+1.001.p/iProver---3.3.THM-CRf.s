%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0674+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:52 EST 2020

% Result     : Theorem 54.05s
% Output     : CNFRefutation 54.05s
% Verified   : 
% Statistics : Number of formulae       :  191 (35827 expanded)
%              Number of clauses        :  149 (10420 expanded)
%              Number of leaves         :   14 (8036 expanded)
%              Depth                    :   41
%              Number of atoms          :  661 (186764 expanded)
%              Number of equality atoms :  376 (75731 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15,f14,f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k11_relat_1(sK5,sK4) != k1_tarski(k1_funct_1(sK5,sK4))
      & r2_hidden(sK4,k1_relat_1(sK5))
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k11_relat_1(sK5,sK4) != k1_tarski(k1_funct_1(sK5,sK4))
    & r2_hidden(sK4,k1_relat_1(sK5))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f21])).

fof(f37,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f41,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f38,plain,(
    r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    k11_relat_1(sK5,sK4) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f46,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f24,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f25,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_487,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2460,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X3,k1_tarski(X1))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_487,c_12])).

cnf(c_486,plain,
    ( X0 != X1
    | sK0(X0,X2,X3) = sK0(X1,X2,X3) ),
    theory(equality)).

cnf(c_6423,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | ~ r2_hidden(sK0(X2,X3,X4),X1)
    | r2_hidden(sK0(X5,X3,X4),X0)
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_2460,c_486])).

cnf(c_482,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2462,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_487,c_482])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_205,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_206,plain,
    ( r2_hidden(sK1(sK5,X0,X1),X0)
    | r2_hidden(sK0(sK5,X0,X1),X1)
    | ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_210,plain,
    ( r2_hidden(sK0(sK5,X0,X1),X1)
    | r2_hidden(sK1(sK5,X0,X1),X0)
    | k9_relat_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_206,c_16])).

cnf(c_211,plain,
    ( r2_hidden(sK1(sK5,X0,X1),X0)
    | r2_hidden(sK0(sK5,X0,X1),X1)
    | k9_relat_1(sK5,X0) = X1 ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_6051,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(sK5,X2,X0),X2)
    | r2_hidden(sK0(sK5,X2,X0),X0)
    | r2_hidden(k9_relat_1(sK5,X2),X1) ),
    inference(resolution,[status(thm)],[c_2462,c_211])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_252,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_248,c_16])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_7245,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(sK1(sK5,X2,k1_funct_1(sK5,X0)),X2)
    | r2_hidden(sK0(sK5,X2,k1_funct_1(sK5,X0)),k1_funct_1(sK5,X0))
    | r2_hidden(k9_relat_1(sK5,X2),k9_relat_1(sK5,X1)) ),
    inference(resolution,[status(thm)],[c_6051,c_253])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19982,plain,
    ( r2_hidden(sK1(sK5,X0,k1_funct_1(sK5,sK4)),X0)
    | r2_hidden(sK0(sK5,X0,k1_funct_1(sK5,sK4)),k1_funct_1(sK5,sK4))
    | r2_hidden(k9_relat_1(sK5,X0),k9_relat_1(sK5,k1_relat_1(sK5)))
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(resolution,[status(thm)],[c_7245,c_14])).

cnf(c_769,plain,
    ( r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_relat_1(sK5)))
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1094,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k9_relat_1(sK5,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_837,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_relat_1(sK5)))
    | X0 != k1_funct_1(sK5,sK4)
    | X1 != k9_relat_1(sK5,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_1093,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,k1_relat_1(sK5)))
    | ~ r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_relat_1(sK5)))
    | X0 != k1_funct_1(sK5,sK4)
    | k9_relat_1(sK5,k1_relat_1(sK5)) != k9_relat_1(sK5,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1796,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_relat_1(sK5)))
    | r2_hidden(k9_relat_1(sK5,X0),k9_relat_1(sK5,k1_relat_1(sK5)))
    | k9_relat_1(sK5,X0) != k1_funct_1(sK5,sK4)
    | k9_relat_1(sK5,k1_relat_1(sK5)) != k9_relat_1(sK5,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1798,plain,
    ( r2_hidden(sK1(sK5,X0,k1_funct_1(sK5,sK4)),X0)
    | r2_hidden(sK0(sK5,X0,k1_funct_1(sK5,sK4)),k1_funct_1(sK5,sK4))
    | k9_relat_1(sK5,X0) = k1_funct_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_20231,plain,
    ( r2_hidden(k9_relat_1(sK5,X0),k9_relat_1(sK5,k1_relat_1(sK5)))
    | r2_hidden(sK0(sK5,X0,k1_funct_1(sK5,sK4)),k1_funct_1(sK5,sK4))
    | r2_hidden(sK1(sK5,X0,k1_funct_1(sK5,sK4)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19982,c_14,c_769,c_1094,c_1796,c_1798])).

cnf(c_20232,plain,
    ( r2_hidden(sK1(sK5,X0,k1_funct_1(sK5,sK4)),X0)
    | r2_hidden(sK0(sK5,X0,k1_funct_1(sK5,sK4)),k1_funct_1(sK5,sK4))
    | r2_hidden(k9_relat_1(sK5,X0),k9_relat_1(sK5,k1_relat_1(sK5))) ),
    inference(renaming,[status(thm)],[c_20231])).

cnf(c_86865,plain,
    ( ~ r2_hidden(X0,k1_tarski(k1_funct_1(sK5,sK4)))
    | r2_hidden(sK1(sK5,X1,k1_funct_1(sK5,sK4)),X1)
    | r2_hidden(sK0(X2,X1,k1_funct_1(sK5,sK4)),X0)
    | r2_hidden(k9_relat_1(sK5,X1),k9_relat_1(sK5,k1_relat_1(sK5)))
    | X2 != sK5 ),
    inference(resolution,[status(thm)],[c_6423,c_20232])).

cnf(c_13,negated_conjecture,
    ( k11_relat_1(sK5,sK4) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_790,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_934,plain,
    ( r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_tarski(sK4)))
    | ~ r2_hidden(sK4,k1_tarski(sK4))
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_964,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_852,plain,
    ( ~ r2_hidden(k1_tarski(k1_funct_1(sK5,sK4)),k1_tarski(X0))
    | k1_tarski(k1_funct_1(sK5,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_979,plain,
    ( ~ r2_hidden(k1_tarski(k1_funct_1(sK5,sK4)),k1_tarski(k1_tarski(k1_funct_1(sK5,sK4))))
    | k1_tarski(k1_funct_1(sK5,sK4)) = k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_980,plain,
    ( r2_hidden(k1_tarski(k1_funct_1(sK5,sK4)),k1_tarski(k1_tarski(k1_funct_1(sK5,sK4)))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1302,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_tarski(sK4)))
    | X0 != k1_funct_1(sK5,sK4)
    | X1 != k9_relat_1(sK5,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_1538,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,k1_tarski(sK4)))
    | ~ r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_tarski(sK4)))
    | X0 != k1_funct_1(sK5,sK4)
    | k9_relat_1(sK5,k1_tarski(sK4)) != k9_relat_1(sK5,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_1539,plain,
    ( k9_relat_1(sK5,k1_tarski(sK4)) = k9_relat_1(sK5,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1781,plain,
    ( ~ r2_hidden(X0,k1_tarski(k1_funct_1(sK5,sK4)))
    | X0 = k1_funct_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_483,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_858,plain,
    ( X0 != X1
    | k1_tarski(k1_funct_1(sK5,sK4)) != X1
    | k1_tarski(k1_funct_1(sK5,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1127,plain,
    ( X0 != k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) = X0
    | k1_tarski(k1_funct_1(sK5,sK4)) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_1824,plain,
    ( k1_tarski(X0) != k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) = k1_tarski(X0)
    | k1_tarski(k1_funct_1(sK5,sK4)) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_491,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_1825,plain,
    ( X0 != k1_funct_1(sK5,sK4)
    | k1_tarski(X0) = k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_2050,plain,
    ( k11_relat_1(sK5,sK4) = k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1836,plain,
    ( k9_relat_1(sK5,X0) != k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) = k9_relat_1(sK5,X0)
    | k1_tarski(k1_funct_1(sK5,sK4)) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_4248,plain,
    ( k9_relat_1(sK5,k1_tarski(sK4)) != k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) = k9_relat_1(sK5,k1_tarski(sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_380,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_381,plain,
    ( k9_relat_1(sK5,k1_tarski(X0)) = k11_relat_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_4900,plain,
    ( k9_relat_1(sK5,k1_tarski(sK4)) = k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_803,plain,
    ( k11_relat_1(sK5,sK4) != X0
    | k11_relat_1(sK5,sK4) = k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_10908,plain,
    ( k11_relat_1(sK5,sK4) != k9_relat_1(sK5,k1_tarski(sK4))
    | k11_relat_1(sK5,sK4) = k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) != k9_relat_1(sK5,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1226,plain,
    ( X0 != X1
    | X0 = k1_tarski(X2)
    | k1_tarski(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_2082,plain,
    ( X0 != k1_tarski(X1)
    | X0 = k1_tarski(X2)
    | k1_tarski(X2) != k1_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_6941,plain,
    ( k9_relat_1(sK5,k1_tarski(sK4)) != k1_tarski(X0)
    | k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(X1)
    | k1_tarski(X1) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_32298,plain,
    ( k9_relat_1(sK5,k1_tarski(sK4)) != k1_tarski(X0)
    | k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_6941])).

cnf(c_1544,plain,
    ( X0 != X1
    | X0 = k9_relat_1(sK5,k1_tarski(sK4))
    | k9_relat_1(sK5,k1_tarski(sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_4899,plain,
    ( X0 != k11_relat_1(sK5,sK4)
    | X0 = k9_relat_1(sK5,k1_tarski(sK4))
    | k9_relat_1(sK5,k1_tarski(sK4)) != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_6241,plain,
    ( k11_relat_1(X0,X1) != k11_relat_1(sK5,sK4)
    | k11_relat_1(X0,X1) = k9_relat_1(sK5,k1_tarski(sK4))
    | k9_relat_1(sK5,k1_tarski(sK4)) != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_4899])).

cnf(c_33381,plain,
    ( k11_relat_1(sK5,sK4) != k11_relat_1(sK5,sK4)
    | k11_relat_1(sK5,sK4) = k9_relat_1(sK5,k1_tarski(sK4))
    | k9_relat_1(sK5,k1_tarski(sK4)) != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6241])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_732,plain,
    ( sK3(X0,X1) = X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | r2_hidden(sK2(sK5,X1,X0),X1)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_318,plain,
    ( r2_hidden(sK2(sK5,X1,X0),X1)
    | ~ r2_hidden(X0,k9_relat_1(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_16])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | r2_hidden(sK2(sK5,X1,X0),X1) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_722,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK2(sK5,X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_730,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1172,plain,
    ( sK2(sK5,k1_tarski(X0),X1) = X0
    | r2_hidden(X1,k9_relat_1(sK5,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_722,c_730])).

cnf(c_1275,plain,
    ( sK2(sK5,k1_tarski(X0),sK3(X1,k9_relat_1(sK5,k1_tarski(X0)))) = X0
    | sK3(X1,k9_relat_1(sK5,k1_tarski(X0))) = X1
    | k9_relat_1(sK5,k1_tarski(X0)) = k1_tarski(X1) ),
    inference(superposition,[status(thm)],[c_732,c_1172])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_332,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK2(sK5,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | k1_funct_1(sK5,sK2(sK5,X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_16])).

cnf(c_721,plain,
    ( k1_funct_1(sK5,sK2(sK5,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK5,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_987,plain,
    ( sK3(X0,k9_relat_1(sK5,X1)) = X0
    | k1_funct_1(sK5,sK2(sK5,X1,sK3(X0,k9_relat_1(sK5,X1)))) = sK3(X0,k9_relat_1(sK5,X1))
    | k9_relat_1(sK5,X1) = k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_732,c_721])).

cnf(c_1664,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = k1_funct_1(sK5,X1)
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_1275,c_987])).

cnf(c_9,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_733,plain,
    ( sK3(X0,X1) != X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10097,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = k1_funct_1(sK5,X1)
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | r2_hidden(sK3(X0,k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_733])).

cnf(c_10420,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = k1_funct_1(sK5,X1)
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | r2_hidden(X0,k9_relat_1(sK5,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_10097])).

cnf(c_35460,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | sK3(sK3(X0,k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))) = k1_funct_1(sK5,X1)
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k9_relat_1(sK5,k1_tarski(X1)))) = k9_relat_1(sK5,k1_tarski(X1)) ),
    inference(superposition,[status(thm)],[c_732,c_10420])).

cnf(c_35556,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) != k1_funct_1(sK5,X1)
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k9_relat_1(sK5,k1_tarski(X1)))) = k9_relat_1(sK5,k1_tarski(X1))
    | r2_hidden(sK3(sK3(X0,k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35460,c_733])).

cnf(c_38334,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k9_relat_1(sK5,k1_tarski(X1)))) = k9_relat_1(sK5,k1_tarski(X1))
    | r2_hidden(sK3(sK3(X0,k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35556,c_1664])).

cnf(c_38340,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | sK3(sK3(X0,k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))) = sK3(X0,k9_relat_1(sK5,k1_tarski(X1)))
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k9_relat_1(sK5,k1_tarski(X1)))) = k9_relat_1(sK5,k1_tarski(X1)) ),
    inference(superposition,[status(thm)],[c_732,c_38334])).

cnf(c_10093,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | r2_hidden(k1_funct_1(sK5,X1),k9_relat_1(sK5,k1_tarski(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_732])).

cnf(c_38350,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k9_relat_1(sK5,k1_tarski(X1)))) = k9_relat_1(sK5,k1_tarski(X1))
    | r2_hidden(k1_funct_1(sK5,X1),k9_relat_1(sK5,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35460,c_38334])).

cnf(c_38431,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k9_relat_1(sK5,k1_tarski(X1)))) = k9_relat_1(sK5,k1_tarski(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38340,c_10093,c_38350])).

cnf(c_731,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_38575,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | r2_hidden(sK3(X0,k9_relat_1(sK5,k1_tarski(X1))),k9_relat_1(sK5,k1_tarski(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_38431,c_731])).

cnf(c_39638,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | r2_hidden(sK3(X0,k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_38575])).

cnf(c_729,plain,
    ( r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_725,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_2418,plain,
    ( sK2(sK5,k1_tarski(X0),k1_funct_1(sK5,X1)) = X0
    | r2_hidden(X1,k1_tarski(X0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_1172])).

cnf(c_7080,plain,
    ( sK2(sK5,k1_tarski(X0),k1_funct_1(sK5,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_2418])).

cnf(c_7120,plain,
    ( sK2(sK5,k1_tarski(sK4),k1_funct_1(sK5,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_729,c_7080])).

cnf(c_7604,plain,
    ( r2_hidden(k1_funct_1(sK5,sK4),k9_relat_1(sK5,k1_tarski(sK4))) != iProver_top
    | r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7120,c_722])).

cnf(c_965,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_7841,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7604,c_965])).

cnf(c_1277,plain,
    ( sK2(sK5,k1_tarski(X0),X1) = X0
    | r2_hidden(X1,k11_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_1172])).

cnf(c_1669,plain,
    ( sK2(sK5,k1_tarski(X0),sK3(X1,k11_relat_1(sK5,X0))) = X0
    | sK3(X1,k11_relat_1(sK5,X0)) = X1
    | k11_relat_1(sK5,X0) = k1_tarski(X1) ),
    inference(superposition,[status(thm)],[c_732,c_1277])).

cnf(c_866,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_tarski(X0),X1)) = X1
    | r2_hidden(X1,k11_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_721])).

cnf(c_2317,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_funct_1(sK5,sK2(sK5,k1_tarski(X1),sK3(X0,k11_relat_1(sK5,X1)))) = sK3(X0,k11_relat_1(sK5,X1)) ),
    inference(superposition,[status(thm)],[c_732,c_866])).

cnf(c_2323,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | sK3(X0,k11_relat_1(sK5,X1)) = k1_funct_1(sK5,X1)
    | k11_relat_1(sK5,X1) = k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_1669,c_2317])).

cnf(c_4046,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = k1_funct_1(sK5,X1)
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | r2_hidden(sK3(X0,k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_733])).

cnf(c_4731,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = k1_funct_1(sK5,X1)
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | r2_hidden(X0,k11_relat_1(sK5,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_4046])).

cnf(c_8993,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | sK3(sK3(X0,k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)) = k1_funct_1(sK5,X1)
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k11_relat_1(sK5,X1))) = k11_relat_1(sK5,X1) ),
    inference(superposition,[status(thm)],[c_732,c_4731])).

cnf(c_9863,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | sK3(X0,k11_relat_1(sK5,X1)) != k1_funct_1(sK5,X1)
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k11_relat_1(sK5,X1))) = k11_relat_1(sK5,X1)
    | r2_hidden(sK3(sK3(X0,k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8993,c_733])).

cnf(c_9885,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k11_relat_1(sK5,X1))) = k11_relat_1(sK5,X1)
    | r2_hidden(sK3(sK3(X0,k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9863,c_2323])).

cnf(c_9891,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | sK3(sK3(X0,k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)) = sK3(X0,k11_relat_1(sK5,X1))
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k11_relat_1(sK5,X1))) = k11_relat_1(sK5,X1) ),
    inference(superposition,[status(thm)],[c_732,c_9885])).

cnf(c_4042,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | r2_hidden(k1_funct_1(sK5,X1),k11_relat_1(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_732])).

cnf(c_9895,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k11_relat_1(sK5,X1))) = k11_relat_1(sK5,X1)
    | r2_hidden(k1_funct_1(sK5,X1),k11_relat_1(sK5,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8993,c_9885])).

cnf(c_10433,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_tarski(sK3(X0,k11_relat_1(sK5,X1))) = k11_relat_1(sK5,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9891,c_4042,c_9895])).

cnf(c_10483,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | r2_hidden(sK3(X0,k11_relat_1(sK5,X1)),k11_relat_1(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10433,c_731])).

cnf(c_986,plain,
    ( sK3(X0,k1_tarski(X1)) = X0
    | sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    inference(superposition,[status(thm)],[c_732,c_730])).

cnf(c_1163,plain,
    ( sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1)
    | r2_hidden(sK3(X0,k1_tarski(X1)),k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_733])).

cnf(c_1437,plain,
    ( sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1)
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_1163])).

cnf(c_20,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2435,plain,
    ( k1_tarski(X0) = k1_tarski(X1)
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1437,c_20,c_491])).

cnf(c_2441,plain,
    ( k1_tarski(sK2(sK5,k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X1,k9_relat_1(sK5,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_722,c_2435])).

cnf(c_25986,plain,
    ( k1_tarski(sK2(sK5,k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X1,k11_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_2441])).

cnf(c_29470,plain,
    ( sK3(X0,k11_relat_1(sK5,X1)) = X0
    | k11_relat_1(sK5,X1) = k1_tarski(X0)
    | k1_tarski(sK2(sK5,k1_tarski(X1),sK3(X0,k11_relat_1(sK5,X1)))) = k1_tarski(X1) ),
    inference(superposition,[status(thm)],[c_10483,c_25986])).

cnf(c_47832,plain,
    ( sK2(sK5,k1_tarski(X0),sK3(X1,k11_relat_1(sK5,X0))) = X2
    | sK3(X1,k11_relat_1(sK5,X0)) = X1
    | k11_relat_1(sK5,X0) = k1_tarski(X1)
    | r2_hidden(X2,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29470,c_730])).

cnf(c_49055,plain,
    ( sK2(sK5,k1_tarski(sK4),sK3(X0,k11_relat_1(sK5,sK4))) = sK4
    | sK3(X0,k11_relat_1(sK5,sK4)) = X0
    | k11_relat_1(sK5,sK4) = k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_7841,c_47832])).

cnf(c_50839,plain,
    ( sK3(X0,k11_relat_1(sK5,sK4)) = X0
    | sK3(X0,k11_relat_1(sK5,sK4)) = k1_funct_1(sK5,sK4)
    | k11_relat_1(sK5,sK4) = k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_49055,c_2317])).

cnf(c_50880,plain,
    ( sK3(X0,k11_relat_1(sK5,sK4)) = X0
    | k11_relat_1(sK5,sK4) = k1_tarski(X0)
    | r2_hidden(k1_funct_1(sK5,sK4),k11_relat_1(sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_50839,c_10483])).

cnf(c_33377,plain,
    ( k11_relat_1(sK5,sK4) != k11_relat_1(sK5,sK4)
    | k11_relat_1(sK5,sK4) = k1_tarski(k1_funct_1(sK5,sK4))
    | k1_tarski(k1_funct_1(sK5,sK4)) != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_50881,plain,
    ( sK3(X0,k11_relat_1(sK5,sK4)) = X0
    | k11_relat_1(sK5,sK4) = k1_tarski(X0)
    | k1_tarski(k1_funct_1(sK5,sK4)) = k11_relat_1(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_50839,c_10433])).

cnf(c_53463,plain,
    ( k11_relat_1(sK5,sK4) = k1_tarski(X0)
    | sK3(X0,k11_relat_1(sK5,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_50880,c_13,c_2050,c_33377,c_50881])).

cnf(c_53464,plain,
    ( sK3(X0,k11_relat_1(sK5,sK4)) = X0
    | k11_relat_1(sK5,sK4) = k1_tarski(X0) ),
    inference(renaming,[status(thm)],[c_53463])).

cnf(c_53471,plain,
    ( k11_relat_1(sK5,sK4) = k1_tarski(X0)
    | r2_hidden(sK3(X0,k11_relat_1(sK5,sK4)),k11_relat_1(sK5,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53464,c_733])).

cnf(c_63213,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(sK4))) = X0
    | k11_relat_1(sK5,sK4) = k1_tarski(X0)
    | k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_39638,c_53471])).

cnf(c_10120,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(X1))) = X0
    | k9_relat_1(sK5,k1_tarski(X1)) = k1_tarski(X0)
    | r2_hidden(k1_funct_1(sK5,X1),k11_relat_1(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_10093])).

cnf(c_53521,plain,
    ( k11_relat_1(sK5,sK4) = k1_tarski(X0)
    | r2_hidden(X0,k11_relat_1(sK5,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53464,c_53471])).

cnf(c_54003,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(sK4))) = X0
    | k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(X0)
    | k1_tarski(k1_funct_1(sK5,sK4)) = k11_relat_1(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_10120,c_53521])).

cnf(c_64327,plain,
    ( sK3(X0,k9_relat_1(sK5,k1_tarski(sK4))) = X0
    | k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63213,c_13,c_2050,c_33377,c_54003])).

cnf(c_64334,plain,
    ( k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(X0)
    | r2_hidden(sK3(X0,k9_relat_1(sK5,k1_tarski(sK4))),k9_relat_1(sK5,k1_tarski(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_64327,c_733])).

cnf(c_64398,plain,
    ( k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(X0)
    | r2_hidden(X0,k9_relat_1(sK5,k1_tarski(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_64327,c_64334])).

cnf(c_64402,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,k1_tarski(sK4)))
    | k9_relat_1(sK5,k1_tarski(sK4)) = k1_tarski(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_64398])).

cnf(c_120405,plain,
    ( ~ r2_hidden(X0,k1_tarski(k1_funct_1(sK5,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_86865,c_14,c_13,c_934,c_964,c_979,c_980,c_1538,c_1539,c_1781,c_1824,c_1825,c_2050,c_4248,c_4900,c_10908,c_32298,c_33381,c_64402])).

cnf(c_120741,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_120405,c_11])).


%------------------------------------------------------------------------------
