%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0595+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:41 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 103 expanded)
%              Number of clauses        :   35 (  43 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 410 expanded)
%              Number of equality atoms :   88 ( 216 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k2_relat_1(X0) = k2_relat_1(X1)
                 => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
          & k2_relat_1(X0) = k2_relat_1(X1)
          & v1_relat_1(X2) )
     => ( k2_relat_1(k5_relat_1(X0,sK2)) != k2_relat_1(k5_relat_1(X1,sK2))
        & k2_relat_1(X0) = k2_relat_1(X1)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k2_relat_1(k5_relat_1(sK1,X2)) != k2_relat_1(k5_relat_1(X0,X2))
            & k2_relat_1(sK1) = k2_relat_1(X0)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
                & k2_relat_1(X0) = k2_relat_1(X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(sK0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(sK0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2))
    & k2_relat_1(sK0) = k2_relat_1(sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9,f8,f7])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,plain,(
    k2_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_53,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_447,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_54,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_356,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK0)) != X0_36
    | k2_relat_1(k5_relat_1(sK0,sK2)) != X0_36
    | k2_relat_1(k5_relat_1(sK0,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_446,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK0)) != k2_relat_1(k5_relat_1(sK0,sK2))
    | k2_relat_1(k5_relat_1(sK0,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0))
    | k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_124,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) != X0_36
    | k2_relat_1(k5_relat_1(sK0,sK2)) != X0_36
    | k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_181,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,X0_36)
    | k2_relat_1(k5_relat_1(sK0,sK2)) != k9_relat_1(sK2,X0_36)
    | k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_315,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK0))
    | k2_relat_1(k5_relat_1(sK0,sK2)) != k9_relat_1(sK2,k2_relat_1(sK0))
    | k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_129,plain,
    ( X0_36 != X1_36
    | k2_relat_1(k5_relat_1(sK1,sK2)) != X1_36
    | k2_relat_1(k5_relat_1(sK1,sK2)) = X0_36 ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_145,plain,
    ( X0_36 != k9_relat_1(sK2,k2_relat_1(sK1))
    | k2_relat_1(k5_relat_1(sK1,sK2)) = X0_36
    | k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_162,plain,
    ( k9_relat_1(sK2,X0_36) != k9_relat_1(sK2,k2_relat_1(sK1))
    | k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,X0_36)
    | k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_267,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK0)) != k9_relat_1(sK2,k2_relat_1(sK1))
    | k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1))
    | k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_3,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_49,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_97,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_52,plain,
    ( ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(X1_35)
    | k9_relat_1(X0_35,k2_relat_1(X1_35)) = k2_relat_1(k5_relat_1(X1_35,X0_35)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_96,plain,
    ( k9_relat_1(X0_35,k2_relat_1(X1_35)) = k2_relat_1(k5_relat_1(X1_35,X0_35))
    | v1_relat_1(X0_35) != iProver_top
    | v1_relat_1(X1_35) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_205,plain,
    ( k9_relat_1(sK2,k2_relat_1(X0_35)) = k2_relat_1(k5_relat_1(X0_35,sK2))
    | v1_relat_1(X0_35) != iProver_top ),
    inference(superposition,[status(thm)],[c_97,c_96])).

cnf(c_221,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,sK2))
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_55,plain,
    ( X0_36 != X1_36
    | k9_relat_1(X0_35,X0_36) = k9_relat_1(X0_35,X1_36) ),
    theory(equality)).

cnf(c_163,plain,
    ( X0_36 != k2_relat_1(sK1)
    | k9_relat_1(sK2,X0_36) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_195,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK0)) = k9_relat_1(sK2,k2_relat_1(sK1))
    | k2_relat_1(sK0) != k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_137,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k2_relat_1(sK1)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_130,plain,
    ( X0_36 != k2_relat_1(k5_relat_1(sK1,sK2))
    | k2_relat_1(k5_relat_1(sK1,sK2)) = X0_36
    | k2_relat_1(k5_relat_1(sK1,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_136,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK1)) != k2_relat_1(k5_relat_1(sK1,sK2))
    | k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1))
    | k2_relat_1(k5_relat_1(sK1,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_131,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_2,negated_conjecture,
    ( k2_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_50,negated_conjecture,
    ( k2_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,negated_conjecture,
    ( k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_51,negated_conjecture,
    ( k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_6,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_447,c_446,c_315,c_267,c_221,c_195,c_137,c_136,c_131,c_50,c_51,c_3,c_4,c_6])).


%------------------------------------------------------------------------------
