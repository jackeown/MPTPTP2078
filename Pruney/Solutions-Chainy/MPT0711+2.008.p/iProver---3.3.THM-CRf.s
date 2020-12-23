%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:43 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 150 expanded)
%              Number of clauses        :   45 (  46 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  335 ( 917 expanded)
%              Number of equality atoms :  112 ( 357 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X0) = k1_relat_1(X1) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & ! [X3] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(X0) = k1_relat_1(X1) )
     => ( k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3)
        & ! [X3] :
            ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,sK3) )
        & k1_relat_1(X0) = k1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k7_relat_1(sK2,X2) != k7_relat_1(X0,X2)
            & ! [X3] :
                ( k1_funct_1(sK2,X3) = k1_funct_1(X0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(sK2) = k1_relat_1(X0) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(sK1,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(sK1,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(sK1) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)
    & ! [X3] :
        ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,sK3) )
    & k1_relat_1(sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f24,f23,f22])).

fof(f40,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
        & r2_hidden(sK0(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ( k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
            & r2_hidden(sK0(X1,X2),k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | r2_hidden(sK0(X1,X2),k1_relat_1(X1))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_183,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_3220,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != X0_42
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != X0_42
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_4574,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(X0_39,X0_41)
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(X0_39,X0_41)
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_3220])).

cnf(c_7267,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_4574])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_165,negated_conjecture,
    ( ~ r2_hidden(X0_41,sK3)
    | k1_funct_1(sK1,X0_41) = k1_funct_1(sK2,X0_41) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3207,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3)
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_170,plain,
    ( ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X0_39)
    | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2696,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k7_relat_1(sK2,X0_40))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_2698,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2696])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_171,plain,
    ( ~ v1_funct_1(X0_39)
    | v1_funct_1(k7_relat_1(X0_39,X0_40))
    | ~ v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2524,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k7_relat_1(X1,X2),X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_167,plain,
    ( ~ r2_hidden(X0_41,k1_relat_1(k7_relat_1(X0_39,X0_40)))
    | ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X0_39)
    | k1_funct_1(k7_relat_1(X0_39,X0_40),X0_41) = k1_funct_1(X0_39,X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2500,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_173,plain,
    ( r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(X0_41,k1_relat_1(k7_relat_1(X0_39,X0_40)))
    | ~ v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2502,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k3_xboole_0(k1_relat_1(X0),X2) != k1_relat_1(X1)
    | k7_relat_1(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_169,plain,
    ( ~ v1_funct_1(X0_39)
    | ~ v1_funct_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | k1_funct_1(X0_39,sK0(X1_39,X0_39)) != k1_funct_1(X1_39,sK0(X1_39,X0_39))
    | k3_xboole_0(k1_relat_1(X0_39),X0_40) != k1_relat_1(X1_39)
    | k7_relat_1(X0_39,X0_40) = X1_39 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1768,plain,
    ( ~ v1_funct_1(X0_39)
    | ~ v1_funct_1(k7_relat_1(X1_39,X0_40))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(k7_relat_1(X1_39,X0_40))
    | k1_funct_1(X0_39,sK0(k7_relat_1(X1_39,X0_40),X0_39)) != k1_funct_1(k7_relat_1(X1_39,X0_40),sK0(k7_relat_1(X1_39,X0_40),X0_39))
    | k3_xboole_0(k1_relat_1(X0_39),X1_40) != k1_relat_1(k7_relat_1(X1_39,X0_40))
    | k7_relat_1(X0_39,X1_40) = k7_relat_1(X1_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_2439,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
    | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0)
    | k7_relat_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_168,plain,
    ( r2_hidden(sK0(X0_39,X1_39),k1_relat_1(X0_39))
    | ~ v1_funct_1(X1_39)
    | ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | k3_xboole_0(k1_relat_1(X1_39),X0_40) != k1_relat_1(X0_39)
    | k7_relat_1(X1_39,X0_40) = X0_39 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1764,plain,
    ( r2_hidden(sK0(k7_relat_1(X0_39,X0_40),X1_39),k1_relat_1(k7_relat_1(X0_39,X0_40)))
    | ~ v1_funct_1(X1_39)
    | ~ v1_funct_1(k7_relat_1(X0_39,X0_40))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(k7_relat_1(X0_39,X0_40))
    | k3_xboole_0(k1_relat_1(X1_39),X1_40) != k1_relat_1(k7_relat_1(X0_39,X0_40))
    | k7_relat_1(X1_39,X1_40) = k7_relat_1(X0_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_2291,plain,
    ( r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
    | ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK1)
    | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_162,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_473,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_172,plain,
    ( ~ v1_relat_1(X0_39)
    | k3_xboole_0(k1_relat_1(X0_39),X0_40) = k1_relat_1(k7_relat_1(X0_39,X0_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_465,plain,
    ( k3_xboole_0(k1_relat_1(X0_39),X0_40) = k1_relat_1(k7_relat_1(X0_39,X0_40))
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_654,plain,
    ( k3_xboole_0(k1_relat_1(sK2),X0_40) = k1_relat_1(k7_relat_1(sK2,X0_40)) ),
    inference(superposition,[status(thm)],[c_473,c_465])).

cnf(c_11,negated_conjecture,
    ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_164,negated_conjecture,
    ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_659,plain,
    ( k3_xboole_0(k1_relat_1(sK1),X0_40) = k1_relat_1(k7_relat_1(sK2,X0_40)) ),
    inference(light_normalisation,[status(thm)],[c_654,c_164])).

cnf(c_662,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK3) = k1_relat_1(k7_relat_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_9,negated_conjecture,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_166,negated_conjecture,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7267,c_3207,c_2698,c_2524,c_2500,c_2502,c_2439,c_2291,c_662,c_166,c_12,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:47:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.87/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/0.98  
% 2.87/0.98  ------  iProver source info
% 2.87/0.98  
% 2.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/0.98  git: non_committed_changes: false
% 2.87/0.98  git: last_make_outside_of_git: false
% 2.87/0.98  
% 2.87/0.98  ------ 
% 2.87/0.98  
% 2.87/0.98  ------ Input Options
% 2.87/0.98  
% 2.87/0.98  --out_options                           all
% 2.87/0.98  --tptp_safe_out                         true
% 2.87/0.98  --problem_path                          ""
% 2.87/0.98  --include_path                          ""
% 2.87/0.98  --clausifier                            res/vclausify_rel
% 2.87/0.98  --clausifier_options                    --mode clausify
% 2.87/0.98  --stdin                                 false
% 2.87/0.98  --stats_out                             all
% 2.87/0.98  
% 2.87/0.98  ------ General Options
% 2.87/0.98  
% 2.87/0.98  --fof                                   false
% 2.87/0.98  --time_out_real                         305.
% 2.87/0.98  --time_out_virtual                      -1.
% 2.87/0.98  --symbol_type_check                     false
% 2.87/0.98  --clausify_out                          false
% 2.87/0.98  --sig_cnt_out                           false
% 2.87/0.98  --trig_cnt_out                          false
% 2.87/0.98  --trig_cnt_out_tolerance                1.
% 2.87/0.98  --trig_cnt_out_sk_spl                   false
% 2.87/0.98  --abstr_cl_out                          false
% 2.87/0.98  
% 2.87/0.98  ------ Global Options
% 2.87/0.98  
% 2.87/0.98  --schedule                              default
% 2.87/0.98  --add_important_lit                     false
% 2.87/0.98  --prop_solver_per_cl                    1000
% 2.87/0.98  --min_unsat_core                        false
% 2.87/0.98  --soft_assumptions                      false
% 2.87/0.98  --soft_lemma_size                       3
% 2.87/0.98  --prop_impl_unit_size                   0
% 2.87/0.98  --prop_impl_unit                        []
% 2.87/0.98  --share_sel_clauses                     true
% 2.87/0.98  --reset_solvers                         false
% 2.87/0.98  --bc_imp_inh                            [conj_cone]
% 2.87/0.98  --conj_cone_tolerance                   3.
% 2.87/0.98  --extra_neg_conj                        none
% 2.87/0.98  --large_theory_mode                     true
% 2.87/0.98  --prolific_symb_bound                   200
% 2.87/0.98  --lt_threshold                          2000
% 2.87/0.98  --clause_weak_htbl                      true
% 2.87/0.98  --gc_record_bc_elim                     false
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing Options
% 2.87/0.98  
% 2.87/0.98  --preprocessing_flag                    true
% 2.87/0.98  --time_out_prep_mult                    0.1
% 2.87/0.98  --splitting_mode                        input
% 2.87/0.98  --splitting_grd                         true
% 2.87/0.98  --splitting_cvd                         false
% 2.87/0.98  --splitting_cvd_svl                     false
% 2.87/0.98  --splitting_nvd                         32
% 2.87/0.98  --sub_typing                            true
% 2.87/0.98  --prep_gs_sim                           true
% 2.87/0.98  --prep_unflatten                        true
% 2.87/0.98  --prep_res_sim                          true
% 2.87/0.98  --prep_upred                            true
% 2.87/0.98  --prep_sem_filter                       exhaustive
% 2.87/0.98  --prep_sem_filter_out                   false
% 2.87/0.98  --pred_elim                             true
% 2.87/0.98  --res_sim_input                         true
% 2.87/0.98  --eq_ax_congr_red                       true
% 2.87/0.98  --pure_diseq_elim                       true
% 2.87/0.98  --brand_transform                       false
% 2.87/0.98  --non_eq_to_eq                          false
% 2.87/0.98  --prep_def_merge                        true
% 2.87/0.98  --prep_def_merge_prop_impl              false
% 2.87/0.98  --prep_def_merge_mbd                    true
% 2.87/0.98  --prep_def_merge_tr_red                 false
% 2.87/0.98  --prep_def_merge_tr_cl                  false
% 2.87/0.98  --smt_preprocessing                     true
% 2.87/0.98  --smt_ac_axioms                         fast
% 2.87/0.98  --preprocessed_out                      false
% 2.87/0.98  --preprocessed_stats                    false
% 2.87/0.98  
% 2.87/0.98  ------ Abstraction refinement Options
% 2.87/0.98  
% 2.87/0.98  --abstr_ref                             []
% 2.87/0.98  --abstr_ref_prep                        false
% 2.87/0.98  --abstr_ref_until_sat                   false
% 2.87/0.98  --abstr_ref_sig_restrict                funpre
% 2.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.98  --abstr_ref_under                       []
% 2.87/0.98  
% 2.87/0.98  ------ SAT Options
% 2.87/0.98  
% 2.87/0.98  --sat_mode                              false
% 2.87/0.98  --sat_fm_restart_options                ""
% 2.87/0.98  --sat_gr_def                            false
% 2.87/0.98  --sat_epr_types                         true
% 2.87/0.98  --sat_non_cyclic_types                  false
% 2.87/0.98  --sat_finite_models                     false
% 2.87/0.98  --sat_fm_lemmas                         false
% 2.87/0.98  --sat_fm_prep                           false
% 2.87/0.98  --sat_fm_uc_incr                        true
% 2.87/0.98  --sat_out_model                         small
% 2.87/0.98  --sat_out_clauses                       false
% 2.87/0.98  
% 2.87/0.98  ------ QBF Options
% 2.87/0.98  
% 2.87/0.98  --qbf_mode                              false
% 2.87/0.98  --qbf_elim_univ                         false
% 2.87/0.98  --qbf_dom_inst                          none
% 2.87/0.98  --qbf_dom_pre_inst                      false
% 2.87/0.98  --qbf_sk_in                             false
% 2.87/0.98  --qbf_pred_elim                         true
% 2.87/0.98  --qbf_split                             512
% 2.87/0.98  
% 2.87/0.98  ------ BMC1 Options
% 2.87/0.98  
% 2.87/0.98  --bmc1_incremental                      false
% 2.87/0.98  --bmc1_axioms                           reachable_all
% 2.87/0.98  --bmc1_min_bound                        0
% 2.87/0.98  --bmc1_max_bound                        -1
% 2.87/0.98  --bmc1_max_bound_default                -1
% 2.87/0.98  --bmc1_symbol_reachability              true
% 2.87/0.98  --bmc1_property_lemmas                  false
% 2.87/0.98  --bmc1_k_induction                      false
% 2.87/0.98  --bmc1_non_equiv_states                 false
% 2.87/0.98  --bmc1_deadlock                         false
% 2.87/0.98  --bmc1_ucm                              false
% 2.87/0.98  --bmc1_add_unsat_core                   none
% 2.87/0.98  --bmc1_unsat_core_children              false
% 2.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.98  --bmc1_out_stat                         full
% 2.87/0.98  --bmc1_ground_init                      false
% 2.87/0.98  --bmc1_pre_inst_next_state              false
% 2.87/0.98  --bmc1_pre_inst_state                   false
% 2.87/0.98  --bmc1_pre_inst_reach_state             false
% 2.87/0.98  --bmc1_out_unsat_core                   false
% 2.87/0.98  --bmc1_aig_witness_out                  false
% 2.87/0.98  --bmc1_verbose                          false
% 2.87/0.98  --bmc1_dump_clauses_tptp                false
% 2.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.98  --bmc1_dump_file                        -
% 2.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.98  --bmc1_ucm_extend_mode                  1
% 2.87/0.98  --bmc1_ucm_init_mode                    2
% 2.87/0.98  --bmc1_ucm_cone_mode                    none
% 2.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.98  --bmc1_ucm_relax_model                  4
% 2.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.98  --bmc1_ucm_layered_model                none
% 2.87/0.98  --bmc1_ucm_max_lemma_size               10
% 2.87/0.98  
% 2.87/0.98  ------ AIG Options
% 2.87/0.98  
% 2.87/0.98  --aig_mode                              false
% 2.87/0.98  
% 2.87/0.98  ------ Instantiation Options
% 2.87/0.98  
% 2.87/0.98  --instantiation_flag                    true
% 2.87/0.98  --inst_sos_flag                         false
% 2.87/0.98  --inst_sos_phase                        true
% 2.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel_side                     num_symb
% 2.87/0.98  --inst_solver_per_active                1400
% 2.87/0.98  --inst_solver_calls_frac                1.
% 2.87/0.98  --inst_passive_queue_type               priority_queues
% 2.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.98  --inst_passive_queues_freq              [25;2]
% 2.87/0.98  --inst_dismatching                      true
% 2.87/0.98  --inst_eager_unprocessed_to_passive     true
% 2.87/0.98  --inst_prop_sim_given                   true
% 2.87/0.98  --inst_prop_sim_new                     false
% 2.87/0.98  --inst_subs_new                         false
% 2.87/0.98  --inst_eq_res_simp                      false
% 2.87/0.98  --inst_subs_given                       false
% 2.87/0.98  --inst_orphan_elimination               true
% 2.87/0.98  --inst_learning_loop_flag               true
% 2.87/0.98  --inst_learning_start                   3000
% 2.87/0.98  --inst_learning_factor                  2
% 2.87/0.98  --inst_start_prop_sim_after_learn       3
% 2.87/0.98  --inst_sel_renew                        solver
% 2.87/0.98  --inst_lit_activity_flag                true
% 2.87/0.98  --inst_restr_to_given                   false
% 2.87/0.98  --inst_activity_threshold               500
% 2.87/0.98  --inst_out_proof                        true
% 2.87/0.98  
% 2.87/0.98  ------ Resolution Options
% 2.87/0.98  
% 2.87/0.98  --resolution_flag                       true
% 2.87/0.98  --res_lit_sel                           adaptive
% 2.87/0.98  --res_lit_sel_side                      none
% 2.87/0.98  --res_ordering                          kbo
% 2.87/0.98  --res_to_prop_solver                    active
% 2.87/0.98  --res_prop_simpl_new                    false
% 2.87/0.98  --res_prop_simpl_given                  true
% 2.87/0.98  --res_passive_queue_type                priority_queues
% 2.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.98  --res_passive_queues_freq               [15;5]
% 2.87/0.98  --res_forward_subs                      full
% 2.87/0.98  --res_backward_subs                     full
% 2.87/0.98  --res_forward_subs_resolution           true
% 2.87/0.98  --res_backward_subs_resolution          true
% 2.87/0.98  --res_orphan_elimination                true
% 2.87/0.98  --res_time_limit                        2.
% 2.87/0.98  --res_out_proof                         true
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Options
% 2.87/0.98  
% 2.87/0.98  --superposition_flag                    true
% 2.87/0.98  --sup_passive_queue_type                priority_queues
% 2.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.98  --demod_completeness_check              fast
% 2.87/0.98  --demod_use_ground                      true
% 2.87/0.98  --sup_to_prop_solver                    passive
% 2.87/0.98  --sup_prop_simpl_new                    true
% 2.87/0.98  --sup_prop_simpl_given                  true
% 2.87/0.98  --sup_fun_splitting                     false
% 2.87/0.98  --sup_smt_interval                      50000
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Simplification Setup
% 2.87/0.98  
% 2.87/0.98  --sup_indices_passive                   []
% 2.87/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_full_bw                           [BwDemod]
% 2.87/0.98  --sup_immed_triv                        [TrivRules]
% 2.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_immed_bw_main                     []
% 2.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  
% 2.87/0.98  ------ Combination Options
% 2.87/0.98  
% 2.87/0.98  --comb_res_mult                         3
% 2.87/0.98  --comb_sup_mult                         2
% 2.87/0.98  --comb_inst_mult                        10
% 2.87/0.98  
% 2.87/0.98  ------ Debug Options
% 2.87/0.98  
% 2.87/0.98  --dbg_backtrace                         false
% 2.87/0.98  --dbg_dump_prop_clauses                 false
% 2.87/0.98  --dbg_dump_prop_clauses_file            -
% 2.87/0.98  --dbg_out_stat                          false
% 2.87/0.98  ------ Parsing...
% 2.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/0.98  ------ Proving...
% 2.87/0.98  ------ Problem Properties 
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  clauses                                 16
% 2.87/0.98  conjectures                             7
% 2.87/0.98  EPR                                     4
% 2.87/0.98  Horn                                    15
% 2.87/0.98  unary                                   6
% 2.87/0.98  binary                                  2
% 2.87/0.98  lits                                    44
% 2.87/0.98  lits eq                                 10
% 2.87/0.98  fd_pure                                 0
% 2.87/0.98  fd_pseudo                               0
% 2.87/0.98  fd_cond                                 0
% 2.87/0.98  fd_pseudo_cond                          2
% 2.87/0.98  AC symbols                              0
% 2.87/0.98  
% 2.87/0.98  ------ Schedule dynamic 5 is on 
% 2.87/0.98  
% 2.87/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  ------ 
% 2.87/0.98  Current options:
% 2.87/0.98  ------ 
% 2.87/0.98  
% 2.87/0.98  ------ Input Options
% 2.87/0.98  
% 2.87/0.98  --out_options                           all
% 2.87/0.98  --tptp_safe_out                         true
% 2.87/0.98  --problem_path                          ""
% 2.87/0.98  --include_path                          ""
% 2.87/0.98  --clausifier                            res/vclausify_rel
% 2.87/0.98  --clausifier_options                    --mode clausify
% 2.87/0.98  --stdin                                 false
% 2.87/0.98  --stats_out                             all
% 2.87/0.98  
% 2.87/0.98  ------ General Options
% 2.87/0.98  
% 2.87/0.98  --fof                                   false
% 2.87/0.98  --time_out_real                         305.
% 2.87/0.98  --time_out_virtual                      -1.
% 2.87/0.98  --symbol_type_check                     false
% 2.87/0.98  --clausify_out                          false
% 2.87/0.98  --sig_cnt_out                           false
% 2.87/0.98  --trig_cnt_out                          false
% 2.87/0.98  --trig_cnt_out_tolerance                1.
% 2.87/0.98  --trig_cnt_out_sk_spl                   false
% 2.87/0.98  --abstr_cl_out                          false
% 2.87/0.98  
% 2.87/0.98  ------ Global Options
% 2.87/0.98  
% 2.87/0.98  --schedule                              default
% 2.87/0.98  --add_important_lit                     false
% 2.87/0.98  --prop_solver_per_cl                    1000
% 2.87/0.98  --min_unsat_core                        false
% 2.87/0.98  --soft_assumptions                      false
% 2.87/0.98  --soft_lemma_size                       3
% 2.87/0.98  --prop_impl_unit_size                   0
% 2.87/0.98  --prop_impl_unit                        []
% 2.87/0.98  --share_sel_clauses                     true
% 2.87/0.98  --reset_solvers                         false
% 2.87/0.98  --bc_imp_inh                            [conj_cone]
% 2.87/0.98  --conj_cone_tolerance                   3.
% 2.87/0.98  --extra_neg_conj                        none
% 2.87/0.98  --large_theory_mode                     true
% 2.87/0.98  --prolific_symb_bound                   200
% 2.87/0.98  --lt_threshold                          2000
% 2.87/0.98  --clause_weak_htbl                      true
% 2.87/0.98  --gc_record_bc_elim                     false
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing Options
% 2.87/0.98  
% 2.87/0.98  --preprocessing_flag                    true
% 2.87/0.98  --time_out_prep_mult                    0.1
% 2.87/0.98  --splitting_mode                        input
% 2.87/0.98  --splitting_grd                         true
% 2.87/0.98  --splitting_cvd                         false
% 2.87/0.98  --splitting_cvd_svl                     false
% 2.87/0.98  --splitting_nvd                         32
% 2.87/0.98  --sub_typing                            true
% 2.87/0.98  --prep_gs_sim                           true
% 2.87/0.98  --prep_unflatten                        true
% 2.87/0.98  --prep_res_sim                          true
% 2.87/0.98  --prep_upred                            true
% 2.87/0.98  --prep_sem_filter                       exhaustive
% 2.87/0.98  --prep_sem_filter_out                   false
% 2.87/0.98  --pred_elim                             true
% 2.87/0.98  --res_sim_input                         true
% 2.87/0.98  --eq_ax_congr_red                       true
% 2.87/0.98  --pure_diseq_elim                       true
% 2.87/0.98  --brand_transform                       false
% 2.87/0.98  --non_eq_to_eq                          false
% 2.87/0.98  --prep_def_merge                        true
% 2.87/0.98  --prep_def_merge_prop_impl              false
% 2.87/0.98  --prep_def_merge_mbd                    true
% 2.87/0.98  --prep_def_merge_tr_red                 false
% 2.87/0.98  --prep_def_merge_tr_cl                  false
% 2.87/0.98  --smt_preprocessing                     true
% 2.87/0.98  --smt_ac_axioms                         fast
% 2.87/0.98  --preprocessed_out                      false
% 2.87/0.98  --preprocessed_stats                    false
% 2.87/0.98  
% 2.87/0.98  ------ Abstraction refinement Options
% 2.87/0.98  
% 2.87/0.98  --abstr_ref                             []
% 2.87/0.98  --abstr_ref_prep                        false
% 2.87/0.98  --abstr_ref_until_sat                   false
% 2.87/0.98  --abstr_ref_sig_restrict                funpre
% 2.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.98  --abstr_ref_under                       []
% 2.87/0.98  
% 2.87/0.98  ------ SAT Options
% 2.87/0.98  
% 2.87/0.98  --sat_mode                              false
% 2.87/0.98  --sat_fm_restart_options                ""
% 2.87/0.98  --sat_gr_def                            false
% 2.87/0.98  --sat_epr_types                         true
% 2.87/0.98  --sat_non_cyclic_types                  false
% 2.87/0.98  --sat_finite_models                     false
% 2.87/0.98  --sat_fm_lemmas                         false
% 2.87/0.98  --sat_fm_prep                           false
% 2.87/0.98  --sat_fm_uc_incr                        true
% 2.87/0.98  --sat_out_model                         small
% 2.87/0.98  --sat_out_clauses                       false
% 2.87/0.98  
% 2.87/0.98  ------ QBF Options
% 2.87/0.98  
% 2.87/0.98  --qbf_mode                              false
% 2.87/0.98  --qbf_elim_univ                         false
% 2.87/0.98  --qbf_dom_inst                          none
% 2.87/0.98  --qbf_dom_pre_inst                      false
% 2.87/0.98  --qbf_sk_in                             false
% 2.87/0.98  --qbf_pred_elim                         true
% 2.87/0.98  --qbf_split                             512
% 2.87/0.98  
% 2.87/0.98  ------ BMC1 Options
% 2.87/0.98  
% 2.87/0.98  --bmc1_incremental                      false
% 2.87/0.98  --bmc1_axioms                           reachable_all
% 2.87/0.98  --bmc1_min_bound                        0
% 2.87/0.98  --bmc1_max_bound                        -1
% 2.87/0.98  --bmc1_max_bound_default                -1
% 2.87/0.98  --bmc1_symbol_reachability              true
% 2.87/0.98  --bmc1_property_lemmas                  false
% 2.87/0.98  --bmc1_k_induction                      false
% 2.87/0.98  --bmc1_non_equiv_states                 false
% 2.87/0.98  --bmc1_deadlock                         false
% 2.87/0.98  --bmc1_ucm                              false
% 2.87/0.98  --bmc1_add_unsat_core                   none
% 2.87/0.98  --bmc1_unsat_core_children              false
% 2.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.98  --bmc1_out_stat                         full
% 2.87/0.98  --bmc1_ground_init                      false
% 2.87/0.98  --bmc1_pre_inst_next_state              false
% 2.87/0.98  --bmc1_pre_inst_state                   false
% 2.87/0.98  --bmc1_pre_inst_reach_state             false
% 2.87/0.98  --bmc1_out_unsat_core                   false
% 2.87/0.98  --bmc1_aig_witness_out                  false
% 2.87/0.98  --bmc1_verbose                          false
% 2.87/0.98  --bmc1_dump_clauses_tptp                false
% 2.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.98  --bmc1_dump_file                        -
% 2.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.98  --bmc1_ucm_extend_mode                  1
% 2.87/0.98  --bmc1_ucm_init_mode                    2
% 2.87/0.98  --bmc1_ucm_cone_mode                    none
% 2.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.98  --bmc1_ucm_relax_model                  4
% 2.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.98  --bmc1_ucm_layered_model                none
% 2.87/0.98  --bmc1_ucm_max_lemma_size               10
% 2.87/0.98  
% 2.87/0.98  ------ AIG Options
% 2.87/0.98  
% 2.87/0.98  --aig_mode                              false
% 2.87/0.98  
% 2.87/0.98  ------ Instantiation Options
% 2.87/0.98  
% 2.87/0.98  --instantiation_flag                    true
% 2.87/0.98  --inst_sos_flag                         false
% 2.87/0.98  --inst_sos_phase                        true
% 2.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel_side                     none
% 2.87/0.98  --inst_solver_per_active                1400
% 2.87/0.98  --inst_solver_calls_frac                1.
% 2.87/0.98  --inst_passive_queue_type               priority_queues
% 2.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.98  --inst_passive_queues_freq              [25;2]
% 2.87/0.98  --inst_dismatching                      true
% 2.87/0.98  --inst_eager_unprocessed_to_passive     true
% 2.87/0.98  --inst_prop_sim_given                   true
% 2.87/0.98  --inst_prop_sim_new                     false
% 2.87/0.98  --inst_subs_new                         false
% 2.87/0.98  --inst_eq_res_simp                      false
% 2.87/0.98  --inst_subs_given                       false
% 2.87/0.98  --inst_orphan_elimination               true
% 2.87/0.98  --inst_learning_loop_flag               true
% 2.87/0.98  --inst_learning_start                   3000
% 2.87/0.98  --inst_learning_factor                  2
% 2.87/0.98  --inst_start_prop_sim_after_learn       3
% 2.87/0.98  --inst_sel_renew                        solver
% 2.87/0.98  --inst_lit_activity_flag                true
% 2.87/0.98  --inst_restr_to_given                   false
% 2.87/0.98  --inst_activity_threshold               500
% 2.87/0.98  --inst_out_proof                        true
% 2.87/0.98  
% 2.87/0.98  ------ Resolution Options
% 2.87/0.98  
% 2.87/0.98  --resolution_flag                       false
% 2.87/0.98  --res_lit_sel                           adaptive
% 2.87/0.98  --res_lit_sel_side                      none
% 2.87/0.98  --res_ordering                          kbo
% 2.87/0.98  --res_to_prop_solver                    active
% 2.87/0.98  --res_prop_simpl_new                    false
% 2.87/0.98  --res_prop_simpl_given                  true
% 2.87/0.98  --res_passive_queue_type                priority_queues
% 2.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.98  --res_passive_queues_freq               [15;5]
% 2.87/0.98  --res_forward_subs                      full
% 2.87/0.98  --res_backward_subs                     full
% 2.87/0.98  --res_forward_subs_resolution           true
% 2.87/0.98  --res_backward_subs_resolution          true
% 2.87/0.98  --res_orphan_elimination                true
% 2.87/0.98  --res_time_limit                        2.
% 2.87/0.98  --res_out_proof                         true
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Options
% 2.87/0.98  
% 2.87/0.98  --superposition_flag                    true
% 2.87/0.98  --sup_passive_queue_type                priority_queues
% 2.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.98  --demod_completeness_check              fast
% 2.87/0.98  --demod_use_ground                      true
% 2.87/0.98  --sup_to_prop_solver                    passive
% 2.87/0.98  --sup_prop_simpl_new                    true
% 2.87/0.98  --sup_prop_simpl_given                  true
% 2.87/0.98  --sup_fun_splitting                     false
% 2.87/0.98  --sup_smt_interval                      50000
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Simplification Setup
% 2.87/0.98  
% 2.87/0.98  --sup_indices_passive                   []
% 2.87/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_full_bw                           [BwDemod]
% 2.87/0.98  --sup_immed_triv                        [TrivRules]
% 2.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_immed_bw_main                     []
% 2.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  
% 2.87/0.98  ------ Combination Options
% 2.87/0.98  
% 2.87/0.98  --comb_res_mult                         3
% 2.87/0.98  --comb_sup_mult                         2
% 2.87/0.98  --comb_inst_mult                        10
% 2.87/0.98  
% 2.87/0.98  ------ Debug Options
% 2.87/0.98  
% 2.87/0.98  --dbg_backtrace                         false
% 2.87/0.98  --dbg_dump_prop_clauses                 false
% 2.87/0.98  --dbg_dump_prop_clauses_file            -
% 2.87/0.98  --dbg_out_stat                          false
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  ------ Proving...
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  % SZS status Theorem for theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  fof(f6,conjecture,(
% 2.87/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f7,negated_conjecture,(
% 2.87/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 2.87/0.98    inference(negated_conjecture,[],[f6])).
% 2.87/0.98  
% 2.87/0.98  fof(f16,plain,(
% 2.87/0.98    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.87/0.98    inference(ennf_transformation,[],[f7])).
% 2.87/0.98  
% 2.87/0.98  fof(f17,plain,(
% 2.87/0.98    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.87/0.98    inference(flattening,[],[f16])).
% 2.87/0.98  
% 2.87/0.98  fof(f24,plain,(
% 2.87/0.98    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => (k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,sK3)) & k1_relat_1(X0) = k1_relat_1(X1))) )),
% 2.87/0.98    introduced(choice_axiom,[])).
% 2.87/0.98  
% 2.87/0.98  fof(f23,plain,(
% 2.87/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK2,X2) != k7_relat_1(X0,X2) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK2) = k1_relat_1(X0)) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 2.87/0.98    introduced(choice_axiom,[])).
% 2.87/0.98  
% 2.87/0.98  fof(f22,plain,(
% 2.87/0.98    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(sK1,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK1) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.87/0.98    introduced(choice_axiom,[])).
% 2.87/0.98  
% 2.87/0.98  fof(f25,plain,(
% 2.87/0.98    ((k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) & ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | ~r2_hidden(X3,sK3)) & k1_relat_1(sK1) = k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f24,f23,f22])).
% 2.87/0.98  
% 2.87/0.98  fof(f40,plain,(
% 2.87/0.98    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | ~r2_hidden(X3,sK3)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f25])).
% 2.87/0.98  
% 2.87/0.98  fof(f3,axiom,(
% 2.87/0.98    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f10,plain,(
% 2.87/0.98    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/0.98    inference(ennf_transformation,[],[f3])).
% 2.87/0.98  
% 2.87/0.98  fof(f11,plain,(
% 2.87/0.98    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.98    inference(flattening,[],[f10])).
% 2.87/0.98  
% 2.87/0.98  fof(f30,plain,(
% 2.87/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f11])).
% 2.87/0.98  
% 2.87/0.98  fof(f31,plain,(
% 2.87/0.98    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f11])).
% 2.87/0.98  
% 2.87/0.98  fof(f5,axiom,(
% 2.87/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f14,plain,(
% 2.87/0.98    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.87/0.98    inference(ennf_transformation,[],[f5])).
% 2.87/0.98  
% 2.87/0.98  fof(f15,plain,(
% 2.87/0.98    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.87/0.98    inference(flattening,[],[f14])).
% 2.87/0.98  
% 2.87/0.98  fof(f34,plain,(
% 2.87/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f15])).
% 2.87/0.98  
% 2.87/0.98  fof(f1,axiom,(
% 2.87/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f8,plain,(
% 2.87/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 2.87/0.98    inference(ennf_transformation,[],[f1])).
% 2.87/0.98  
% 2.87/0.98  fof(f18,plain,(
% 2.87/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.87/0.98    inference(nnf_transformation,[],[f8])).
% 2.87/0.98  
% 2.87/0.98  fof(f19,plain,(
% 2.87/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.87/0.98    inference(flattening,[],[f18])).
% 2.87/0.98  
% 2.87/0.98  fof(f26,plain,(
% 2.87/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f19])).
% 2.87/0.98  
% 2.87/0.98  fof(f4,axiom,(
% 2.87/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f12,plain,(
% 2.87/0.98    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.87/0.98    inference(ennf_transformation,[],[f4])).
% 2.87/0.98  
% 2.87/0.98  fof(f13,plain,(
% 2.87/0.98    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.87/0.98    inference(flattening,[],[f12])).
% 2.87/0.98  
% 2.87/0.98  fof(f20,plain,(
% 2.87/0.98    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) & r2_hidden(sK0(X1,X2),k1_relat_1(X1))))),
% 2.87/0.98    introduced(choice_axiom,[])).
% 2.87/0.98  
% 2.87/0.98  fof(f21,plain,(
% 2.87/0.98    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) & r2_hidden(sK0(X1,X2),k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).
% 2.87/0.98  
% 2.87/0.98  fof(f33,plain,(
% 2.87/0.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f21])).
% 2.87/0.98  
% 2.87/0.98  fof(f32,plain,(
% 2.87/0.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | r2_hidden(sK0(X1,X2),k1_relat_1(X1)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f21])).
% 2.87/0.98  
% 2.87/0.98  fof(f37,plain,(
% 2.87/0.98    v1_relat_1(sK2)),
% 2.87/0.98    inference(cnf_transformation,[],[f25])).
% 2.87/0.98  
% 2.87/0.98  fof(f2,axiom,(
% 2.87/0.98    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f9,plain,(
% 2.87/0.98    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.87/0.98    inference(ennf_transformation,[],[f2])).
% 2.87/0.98  
% 2.87/0.98  fof(f29,plain,(
% 2.87/0.98    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f9])).
% 2.87/0.98  
% 2.87/0.98  fof(f39,plain,(
% 2.87/0.98    k1_relat_1(sK1) = k1_relat_1(sK2)),
% 2.87/0.98    inference(cnf_transformation,[],[f25])).
% 2.87/0.98  
% 2.87/0.98  fof(f41,plain,(
% 2.87/0.98    k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)),
% 2.87/0.98    inference(cnf_transformation,[],[f25])).
% 2.87/0.98  
% 2.87/0.98  fof(f38,plain,(
% 2.87/0.98    v1_funct_1(sK2)),
% 2.87/0.98    inference(cnf_transformation,[],[f25])).
% 2.87/0.98  
% 2.87/0.98  fof(f36,plain,(
% 2.87/0.98    v1_funct_1(sK1)),
% 2.87/0.98    inference(cnf_transformation,[],[f25])).
% 2.87/0.98  
% 2.87/0.98  fof(f35,plain,(
% 2.87/0.98    v1_relat_1(sK1)),
% 2.87/0.98    inference(cnf_transformation,[],[f25])).
% 2.87/0.98  
% 2.87/0.98  cnf(c_183,plain,
% 2.87/0.98      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 2.87/0.98      theory(equality) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_3220,plain,
% 2.87/0.98      ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != X0_42
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != X0_42
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_183]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_4574,plain,
% 2.87/0.98      ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(X0_39,X0_41)
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(X0_39,X0_41)
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_3220]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_7267,plain,
% 2.87/0.98      ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_4574]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_10,negated_conjecture,
% 2.87/0.98      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ),
% 2.87/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_165,negated_conjecture,
% 2.87/0.98      ( ~ r2_hidden(X0_41,sK3)
% 2.87/0.98      | k1_funct_1(sK1,X0_41) = k1_funct_1(sK2,X0_41) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_3207,plain,
% 2.87/0.98      ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3)
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_165]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_5,plain,
% 2.87/0.98      ( ~ v1_funct_1(X0)
% 2.87/0.98      | ~ v1_relat_1(X0)
% 2.87/0.98      | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.87/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_170,plain,
% 2.87/0.98      ( ~ v1_funct_1(X0_39)
% 2.87/0.98      | ~ v1_relat_1(X0_39)
% 2.87/0.98      | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2696,plain,
% 2.87/0.98      ( ~ v1_funct_1(sK2)
% 2.87/0.98      | v1_relat_1(k7_relat_1(sK2,X0_40))
% 2.87/0.98      | ~ v1_relat_1(sK2) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_170]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2698,plain,
% 2.87/0.98      ( ~ v1_funct_1(sK2)
% 2.87/0.98      | v1_relat_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | ~ v1_relat_1(sK2) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_2696]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_4,plain,
% 2.87/0.98      ( ~ v1_funct_1(X0)
% 2.87/0.98      | v1_funct_1(k7_relat_1(X0,X1))
% 2.87/0.98      | ~ v1_relat_1(X0) ),
% 2.87/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_171,plain,
% 2.87/0.98      ( ~ v1_funct_1(X0_39)
% 2.87/0.98      | v1_funct_1(k7_relat_1(X0_39,X0_40))
% 2.87/0.98      | ~ v1_relat_1(X0_39) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2524,plain,
% 2.87/0.98      ( v1_funct_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | ~ v1_funct_1(sK2)
% 2.87/0.98      | ~ v1_relat_1(sK2) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_171]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_8,plain,
% 2.87/0.98      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 2.87/0.98      | ~ v1_funct_1(X1)
% 2.87/0.98      | ~ v1_relat_1(X1)
% 2.87/0.98      | k1_funct_1(k7_relat_1(X1,X2),X0) = k1_funct_1(X1,X0) ),
% 2.87/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_167,plain,
% 2.87/0.98      ( ~ r2_hidden(X0_41,k1_relat_1(k7_relat_1(X0_39,X0_40)))
% 2.87/0.98      | ~ v1_funct_1(X0_39)
% 2.87/0.98      | ~ v1_relat_1(X0_39)
% 2.87/0.98      | k1_funct_1(k7_relat_1(X0_39,X0_40),X0_41) = k1_funct_1(X0_39,X0_41) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2500,plain,
% 2.87/0.98      ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
% 2.87/0.98      | ~ v1_funct_1(sK2)
% 2.87/0.98      | ~ v1_relat_1(sK2)
% 2.87/0.98      | k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_167]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2,plain,
% 2.87/0.98      ( r2_hidden(X0,X1)
% 2.87/0.98      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 2.87/0.98      | ~ v1_relat_1(X2) ),
% 2.87/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_173,plain,
% 2.87/0.98      ( r2_hidden(X0_41,X0_40)
% 2.87/0.98      | ~ r2_hidden(X0_41,k1_relat_1(k7_relat_1(X0_39,X0_40)))
% 2.87/0.98      | ~ v1_relat_1(X0_39) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2502,plain,
% 2.87/0.98      ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
% 2.87/0.98      | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3)
% 2.87/0.98      | ~ v1_relat_1(sK2) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_173]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_6,plain,
% 2.87/0.98      ( ~ v1_funct_1(X0)
% 2.87/0.98      | ~ v1_funct_1(X1)
% 2.87/0.98      | ~ v1_relat_1(X0)
% 2.87/0.98      | ~ v1_relat_1(X1)
% 2.87/0.98      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X0),X2) != k1_relat_1(X1)
% 2.87/0.98      | k7_relat_1(X0,X2) = X1 ),
% 2.87/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_169,plain,
% 2.87/0.98      ( ~ v1_funct_1(X0_39)
% 2.87/0.98      | ~ v1_funct_1(X1_39)
% 2.87/0.98      | ~ v1_relat_1(X0_39)
% 2.87/0.98      | ~ v1_relat_1(X1_39)
% 2.87/0.98      | k1_funct_1(X0_39,sK0(X1_39,X0_39)) != k1_funct_1(X1_39,sK0(X1_39,X0_39))
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X0_39),X0_40) != k1_relat_1(X1_39)
% 2.87/0.98      | k7_relat_1(X0_39,X0_40) = X1_39 ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1768,plain,
% 2.87/0.98      ( ~ v1_funct_1(X0_39)
% 2.87/0.98      | ~ v1_funct_1(k7_relat_1(X1_39,X0_40))
% 2.87/0.98      | ~ v1_relat_1(X0_39)
% 2.87/0.98      | ~ v1_relat_1(k7_relat_1(X1_39,X0_40))
% 2.87/0.98      | k1_funct_1(X0_39,sK0(k7_relat_1(X1_39,X0_40),X0_39)) != k1_funct_1(k7_relat_1(X1_39,X0_40),sK0(k7_relat_1(X1_39,X0_40),X0_39))
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X0_39),X1_40) != k1_relat_1(k7_relat_1(X1_39,X0_40))
% 2.87/0.98      | k7_relat_1(X0_39,X1_40) = k7_relat_1(X1_39,X0_40) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_169]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2439,plain,
% 2.87/0.98      ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | ~ v1_funct_1(sK1)
% 2.87/0.98      | ~ v1_relat_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | ~ v1_relat_1(sK1)
% 2.87/0.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
% 2.87/0.98      | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_1768]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_7,plain,
% 2.87/0.98      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.87/0.98      | ~ v1_funct_1(X1)
% 2.87/0.98      | ~ v1_funct_1(X0)
% 2.87/0.98      | ~ v1_relat_1(X1)
% 2.87/0.98      | ~ v1_relat_1(X0)
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0)
% 2.87/0.98      | k7_relat_1(X1,X2) = X0 ),
% 2.87/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_168,plain,
% 2.87/0.98      ( r2_hidden(sK0(X0_39,X1_39),k1_relat_1(X0_39))
% 2.87/0.98      | ~ v1_funct_1(X1_39)
% 2.87/0.98      | ~ v1_funct_1(X0_39)
% 2.87/0.98      | ~ v1_relat_1(X1_39)
% 2.87/0.98      | ~ v1_relat_1(X0_39)
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X1_39),X0_40) != k1_relat_1(X0_39)
% 2.87/0.98      | k7_relat_1(X1_39,X0_40) = X0_39 ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1764,plain,
% 2.87/0.98      ( r2_hidden(sK0(k7_relat_1(X0_39,X0_40),X1_39),k1_relat_1(k7_relat_1(X0_39,X0_40)))
% 2.87/0.98      | ~ v1_funct_1(X1_39)
% 2.87/0.98      | ~ v1_funct_1(k7_relat_1(X0_39,X0_40))
% 2.87/0.98      | ~ v1_relat_1(X1_39)
% 2.87/0.98      | ~ v1_relat_1(k7_relat_1(X0_39,X0_40))
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X1_39),X1_40) != k1_relat_1(k7_relat_1(X0_39,X0_40))
% 2.87/0.98      | k7_relat_1(X1_39,X1_40) = k7_relat_1(X0_39,X0_40) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_168]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_2291,plain,
% 2.87/0.98      ( r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
% 2.87/0.98      | ~ v1_funct_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | ~ v1_funct_1(sK1)
% 2.87/0.98      | ~ v1_relat_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | ~ v1_relat_1(sK1)
% 2.87/0.98      | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
% 2.87/0.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_1764]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_13,negated_conjecture,
% 2.87/0.98      ( v1_relat_1(sK2) ),
% 2.87/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_162,negated_conjecture,
% 2.87/0.98      ( v1_relat_1(sK2) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_473,plain,
% 2.87/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_3,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0)
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 2.87/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_172,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0_39)
% 2.87/0.98      | k3_xboole_0(k1_relat_1(X0_39),X0_40) = k1_relat_1(k7_relat_1(X0_39,X0_40)) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_465,plain,
% 2.87/0.98      ( k3_xboole_0(k1_relat_1(X0_39),X0_40) = k1_relat_1(k7_relat_1(X0_39,X0_40))
% 2.87/0.98      | v1_relat_1(X0_39) != iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_172]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_654,plain,
% 2.87/0.98      ( k3_xboole_0(k1_relat_1(sK2),X0_40) = k1_relat_1(k7_relat_1(sK2,X0_40)) ),
% 2.87/0.98      inference(superposition,[status(thm)],[c_473,c_465]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_11,negated_conjecture,
% 2.87/0.98      ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
% 2.87/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_164,negated_conjecture,
% 2.87/0.98      ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_659,plain,
% 2.87/0.98      ( k3_xboole_0(k1_relat_1(sK1),X0_40) = k1_relat_1(k7_relat_1(sK2,X0_40)) ),
% 2.87/0.98      inference(light_normalisation,[status(thm)],[c_654,c_164]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_662,plain,
% 2.87/0.98      ( k3_xboole_0(k1_relat_1(sK1),sK3) = k1_relat_1(k7_relat_1(sK2,sK3)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_659]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_9,negated_conjecture,
% 2.87/0.98      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 2.87/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_166,negated_conjecture,
% 2.87/0.98      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_12,negated_conjecture,
% 2.87/0.98      ( v1_funct_1(sK2) ),
% 2.87/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_14,negated_conjecture,
% 2.87/0.98      ( v1_funct_1(sK1) ),
% 2.87/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_15,negated_conjecture,
% 2.87/0.98      ( v1_relat_1(sK1) ),
% 2.87/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(contradiction,plain,
% 2.87/0.98      ( $false ),
% 2.87/0.98      inference(minisat,
% 2.87/0.98                [status(thm)],
% 2.87/0.98                [c_7267,c_3207,c_2698,c_2524,c_2500,c_2502,c_2439,c_2291,
% 2.87/0.98                 c_662,c_166,c_12,c_13,c_14,c_15]) ).
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  ------                               Statistics
% 2.87/0.98  
% 2.87/0.98  ------ General
% 2.87/0.98  
% 2.87/0.98  abstr_ref_over_cycles:                  0
% 2.87/0.98  abstr_ref_under_cycles:                 0
% 2.87/0.98  gc_basic_clause_elim:                   0
% 2.87/0.98  forced_gc_time:                         0
% 2.87/0.98  parsing_time:                           0.042
% 2.87/0.98  unif_index_cands_time:                  0.
% 2.87/0.98  unif_index_add_time:                    0.
% 2.87/0.98  orderings_time:                         0.
% 2.87/0.98  out_proof_time:                         0.007
% 2.87/0.98  total_time:                             0.307
% 2.87/0.98  num_of_symbols:                         46
% 2.87/0.98  num_of_terms:                           5572
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing
% 2.87/0.98  
% 2.87/0.98  num_of_splits:                          0
% 2.87/0.98  num_of_split_atoms:                     0
% 2.87/0.98  num_of_reused_defs:                     0
% 2.87/0.98  num_eq_ax_congr_red:                    6
% 2.87/0.98  num_of_sem_filtered_clauses:            1
% 2.87/0.98  num_of_subtypes:                        4
% 2.87/0.98  monotx_restored_types:                  0
% 2.87/0.98  sat_num_of_epr_types:                   0
% 2.87/0.98  sat_num_of_non_cyclic_types:            0
% 2.87/0.98  sat_guarded_non_collapsed_types:        1
% 2.87/0.98  num_pure_diseq_elim:                    0
% 2.87/0.98  simp_replaced_by:                       0
% 2.87/0.98  res_preprocessed:                       77
% 2.87/0.98  prep_upred:                             0
% 2.87/0.98  prep_unflattend:                        0
% 2.87/0.98  smt_new_axioms:                         0
% 2.87/0.98  pred_elim_cands:                        3
% 2.87/0.98  pred_elim:                              0
% 2.87/0.98  pred_elim_cl:                           0
% 2.87/0.98  pred_elim_cycles:                       1
% 2.87/0.98  merged_defs:                            0
% 2.87/0.98  merged_defs_ncl:                        0
% 2.87/0.98  bin_hyper_res:                          0
% 2.87/0.98  prep_cycles:                            3
% 2.87/0.98  pred_elim_time:                         0.
% 2.87/0.98  splitting_time:                         0.
% 2.87/0.98  sem_filter_time:                        0.
% 2.87/0.98  monotx_time:                            0.
% 2.87/0.98  subtype_inf_time:                       0.
% 2.87/0.98  
% 2.87/0.98  ------ Problem properties
% 2.87/0.98  
% 2.87/0.98  clauses:                                16
% 2.87/0.98  conjectures:                            7
% 2.87/0.98  epr:                                    4
% 2.87/0.98  horn:                                   15
% 2.87/0.98  ground:                                 6
% 2.87/0.98  unary:                                  6
% 2.87/0.98  binary:                                 2
% 2.87/0.98  lits:                                   44
% 2.87/0.98  lits_eq:                                10
% 2.87/0.98  fd_pure:                                0
% 2.87/0.98  fd_pseudo:                              0
% 2.87/0.98  fd_cond:                                0
% 2.87/0.98  fd_pseudo_cond:                         2
% 2.87/0.98  ac_symbols:                             0
% 2.87/0.98  
% 2.87/0.98  ------ Propositional Solver
% 2.87/0.98  
% 2.87/0.98  prop_solver_calls:                      30
% 2.87/0.98  prop_fast_solver_calls:                 799
% 2.87/0.98  smt_solver_calls:                       0
% 2.87/0.98  smt_fast_solver_calls:                  0
% 2.87/0.98  prop_num_of_clauses:                    1882
% 2.87/0.98  prop_preprocess_simplified:             4375
% 2.87/0.98  prop_fo_subsumed:                       32
% 2.87/0.98  prop_solver_time:                       0.
% 2.87/0.98  smt_solver_time:                        0.
% 2.87/0.98  smt_fast_solver_time:                   0.
% 2.87/0.98  prop_fast_solver_time:                  0.
% 2.87/0.98  prop_unsat_core_time:                   0.
% 2.87/0.98  
% 2.87/0.98  ------ QBF
% 2.87/0.98  
% 2.87/0.98  qbf_q_res:                              0
% 2.87/0.98  qbf_num_tautologies:                    0
% 2.87/0.98  qbf_prep_cycles:                        0
% 2.87/0.98  
% 2.87/0.98  ------ BMC1
% 2.87/0.98  
% 2.87/0.98  bmc1_current_bound:                     -1
% 2.87/0.98  bmc1_last_solved_bound:                 -1
% 2.87/0.98  bmc1_unsat_core_size:                   -1
% 2.87/0.98  bmc1_unsat_core_parents_size:           -1
% 2.87/0.98  bmc1_merge_next_fun:                    0
% 2.87/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.87/0.98  
% 2.87/0.98  ------ Instantiation
% 2.87/0.98  
% 2.87/0.98  inst_num_of_clauses:                    552
% 2.87/0.98  inst_num_in_passive:                    183
% 2.87/0.98  inst_num_in_active:                     341
% 2.87/0.98  inst_num_in_unprocessed:                27
% 2.87/0.98  inst_num_of_loops:                      374
% 2.87/0.98  inst_num_of_learning_restarts:          0
% 2.87/0.98  inst_num_moves_active_passive:          24
% 2.87/0.98  inst_lit_activity:                      0
% 2.87/0.98  inst_lit_activity_moves:                0
% 2.87/0.98  inst_num_tautologies:                   0
% 2.87/0.98  inst_num_prop_implied:                  0
% 2.87/0.98  inst_num_existing_simplified:           0
% 2.87/0.98  inst_num_eq_res_simplified:             0
% 2.87/0.98  inst_num_child_elim:                    0
% 2.87/0.98  inst_num_of_dismatching_blockings:      887
% 2.87/0.98  inst_num_of_non_proper_insts:           1166
% 2.87/0.98  inst_num_of_duplicates:                 0
% 2.87/0.98  inst_inst_num_from_inst_to_res:         0
% 2.87/0.98  inst_dismatching_checking_time:         0.
% 2.87/0.98  
% 2.87/0.98  ------ Resolution
% 2.87/0.98  
% 2.87/0.98  res_num_of_clauses:                     0
% 2.87/0.98  res_num_in_passive:                     0
% 2.87/0.98  res_num_in_active:                      0
% 2.87/0.98  res_num_of_loops:                       80
% 2.87/0.98  res_forward_subset_subsumed:            144
% 2.87/0.98  res_backward_subset_subsumed:           2
% 2.87/0.98  res_forward_subsumed:                   0
% 2.87/0.98  res_backward_subsumed:                  0
% 2.87/0.98  res_forward_subsumption_resolution:     0
% 2.87/0.98  res_backward_subsumption_resolution:    0
% 2.87/0.98  res_clause_to_clause_subsumption:       1116
% 2.87/0.98  res_orphan_elimination:                 0
% 2.87/0.98  res_tautology_del:                      168
% 2.87/0.98  res_num_eq_res_simplified:              0
% 2.87/0.98  res_num_sel_changes:                    0
% 2.87/0.98  res_moves_from_active_to_pass:          0
% 2.87/0.98  
% 2.87/0.98  ------ Superposition
% 2.87/0.98  
% 2.87/0.98  sup_time_total:                         0.
% 2.87/0.98  sup_time_generating:                    0.
% 2.87/0.98  sup_time_sim_full:                      0.
% 2.87/0.98  sup_time_sim_immed:                     0.
% 2.87/0.98  
% 2.87/0.98  sup_num_of_clauses:                     181
% 2.87/0.98  sup_num_in_active:                      73
% 2.87/0.98  sup_num_in_passive:                     108
% 2.87/0.98  sup_num_of_loops:                       74
% 2.87/0.98  sup_fw_superposition:                   129
% 2.87/0.98  sup_bw_superposition:                   52
% 2.87/0.98  sup_immediate_simplified:               47
% 2.87/0.98  sup_given_eliminated:                   0
% 2.87/0.98  comparisons_done:                       0
% 2.87/0.98  comparisons_avoided:                    20
% 2.87/0.98  
% 2.87/0.98  ------ Simplifications
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  sim_fw_subset_subsumed:                 6
% 2.87/0.98  sim_bw_subset_subsumed:                 1
% 2.87/0.98  sim_fw_subsumed:                        1
% 2.87/0.98  sim_bw_subsumed:                        1
% 2.87/0.98  sim_fw_subsumption_res:                 9
% 2.87/0.98  sim_bw_subsumption_res:                 0
% 2.87/0.98  sim_tautology_del:                      13
% 2.87/0.98  sim_eq_tautology_del:                   1
% 2.87/0.98  sim_eq_res_simp:                        0
% 2.87/0.98  sim_fw_demodulated:                     8
% 2.87/0.98  sim_bw_demodulated:                     1
% 2.87/0.98  sim_light_normalised:                   36
% 2.87/0.98  sim_joinable_taut:                      0
% 2.87/0.98  sim_joinable_simp:                      0
% 2.87/0.98  sim_ac_normalised:                      0
% 2.87/0.98  sim_smt_subsumption:                    0
% 2.87/0.98  
%------------------------------------------------------------------------------
