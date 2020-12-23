%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0748+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:02 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   46 (  56 expanded)
%              Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 185 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
    ? [X1] :
      ( r2_hidden(X1,X0)
    <~> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ( ~ v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) )
      & ( v3_ordinal1(X1)
        | r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_ordinal1(X1)
            | ~ r2_hidden(X1,X0) )
          & ( v3_ordinal1(X1)
            | r2_hidden(X1,X0) ) )
     => ( ( ~ v3_ordinal1(sK1(X0))
          | ~ r2_hidden(sK1(X0),X0) )
        & ( v3_ordinal1(sK1(X0))
          | r2_hidden(sK1(X0),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ( ~ v3_ordinal1(sK1(X0))
        | ~ r2_hidden(sK1(X0),X0) )
      & ( v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f12])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | ~ r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK0(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK0(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK0(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f18,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK0(X0))
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( v3_ordinal1(X1)
           => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,
    ( ? [X0] :
      ! [X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
   => ! [X1] :
        ( r2_hidden(X1,sK2)
        | ~ v3_ordinal1(X1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ v3_ordinal1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f14])).

fof(f21,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(X0))
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X2,X0] :
      ( v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK0(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0),X0)
    | ~ v3_ordinal1(sK1(X0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_158,plain,
    ( ~ r2_hidden(sK1(X0_34),X0_34)
    | ~ v3_ordinal1(sK1(X0_34)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_216,plain,
    ( ~ r2_hidden(sK1(sK0(X0_34)),sK0(X0_34))
    | ~ v3_ordinal1(sK1(sK0(X0_34))) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_217,plain,
    ( r2_hidden(sK1(sK0(X0_34)),sK0(X0_34)) != iProver_top
    | v3_ordinal1(sK1(sK0(X0_34))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_219,plain,
    ( r2_hidden(sK1(sK0(sK2)),sK0(sK2)) != iProver_top
    | v3_ordinal1(sK1(sK0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK0(X1))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_161,plain,
    ( ~ r2_hidden(X0_33,X0_34)
    | r2_hidden(X0_33,sK0(X0_34))
    | ~ v3_ordinal1(X0_33) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_206,plain,
    ( ~ r2_hidden(sK1(sK0(X0_34)),X1_34)
    | r2_hidden(sK1(sK0(X0_34)),sK0(X1_34))
    | ~ v3_ordinal1(sK1(sK0(X0_34))) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_212,plain,
    ( r2_hidden(sK1(sK0(X0_34)),X1_34) != iProver_top
    | r2_hidden(sK1(sK0(X0_34)),sK0(X1_34)) = iProver_top
    | v3_ordinal1(sK1(sK0(X0_34))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_214,plain,
    ( r2_hidden(sK1(sK0(sK2)),sK0(sK2)) = iProver_top
    | r2_hidden(sK1(sK0(sK2)),sK2) != iProver_top
    | v3_ordinal1(sK1(sK0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(X0,sK2)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_156,negated_conjecture,
    ( r2_hidden(X0_33,sK2)
    | ~ v3_ordinal1(X0_33) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_207,plain,
    ( r2_hidden(sK1(sK0(X0_34)),sK2)
    | ~ v3_ordinal1(sK1(sK0(X0_34))) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_208,plain,
    ( r2_hidden(sK1(sK0(X0_34)),sK2) = iProver_top
    | v3_ordinal1(sK1(sK0(X0_34))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_210,plain,
    ( r2_hidden(sK1(sK0(sK2)),sK2) = iProver_top
    | v3_ordinal1(sK1(sK0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | v3_ordinal1(sK1(X0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_157,plain,
    ( r2_hidden(sK1(X0_34),X0_34)
    | v3_ordinal1(sK1(X0_34)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_195,plain,
    ( r2_hidden(sK1(sK0(X0_34)),sK0(X0_34))
    | v3_ordinal1(sK1(sK0(X0_34))) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_200,plain,
    ( r2_hidden(sK1(sK0(X0_34)),sK0(X0_34)) = iProver_top
    | v3_ordinal1(sK1(sK0(X0_34))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_202,plain,
    ( r2_hidden(sK1(sK0(sK2)),sK0(sK2)) = iProver_top
    | v3_ordinal1(sK1(sK0(sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,sK0(X1))
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_160,plain,
    ( ~ r2_hidden(X0_33,sK0(X0_34))
    | v3_ordinal1(X0_33) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_194,plain,
    ( ~ r2_hidden(sK1(sK0(X0_34)),sK0(X0_34))
    | v3_ordinal1(sK1(sK0(X0_34))) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_196,plain,
    ( r2_hidden(sK1(sK0(X0_34)),sK0(X0_34)) != iProver_top
    | v3_ordinal1(sK1(sK0(X0_34))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_198,plain,
    ( r2_hidden(sK1(sK0(sK2)),sK0(sK2)) != iProver_top
    | v3_ordinal1(sK1(sK0(sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_219,c_214,c_210,c_202,c_198])).


%------------------------------------------------------------------------------
