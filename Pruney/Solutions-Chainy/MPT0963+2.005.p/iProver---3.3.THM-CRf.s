%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:18 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 471 expanded)
%              Number of clauses        :   54 ( 140 expanded)
%              Number of leaves         :   12 ( 105 expanded)
%              Depth                    :   23
%              Number of atoms          :  351 (2895 expanded)
%              Number of equality atoms :  108 ( 482 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & ! [X3] :
            ( r2_hidden(k1_funct_1(X2,X3),X1)
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(X2) = X0
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
        | ~ v1_funct_2(sK6,sK4,sK5)
        | ~ v1_funct_1(sK6) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK6,X3),sK5)
          | ~ r2_hidden(X3,sK4) )
      & k1_relat_1(sK6) = sK4
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_2(sK6,sK4,sK5)
      | ~ v1_funct_1(sK6) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK6,X3),sK5)
        | ~ r2_hidden(X3,sK4) )
    & k1_relat_1(sK6) = sK4
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f13,f22])).

fof(f37,plain,(
    k1_relat_1(sK6) = sK4 ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f20,f19,f18])).

fof(f26,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f36,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK6,X3),sK5)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_13,negated_conjecture,
    ( k1_relat_1(sK6) = sK4 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_266,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_271,plain,
    ( r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
    | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_267,c_15])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_663,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_972,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_663])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_668,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_15])).

cnf(c_662,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_836,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_662])).

cnf(c_9,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_87,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_14])).

cnf(c_88,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(renaming,[status(thm)],[c_87])).

cnf(c_174,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_88])).

cnf(c_175,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),X0)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_179,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_175,c_15,c_14])).

cnf(c_199,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(sK6),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_relat_1(X0) != sK4
    | sK5 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_179])).

cnf(c_200,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),X0)
    | ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_relat_1(sK6) != sK4 ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_204,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(k2_relat_1(sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_15,c_14,c_13])).

cnf(c_205,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),X0)
    | ~ r1_tarski(k2_relat_1(sK6),sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_204])).

cnf(c_666,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_456,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_800,plain,
    ( X0 != sK5
    | k2_zfmisc_1(k1_relat_1(sK6),X0) = k2_zfmisc_1(sK4,sK5)
    | k1_relat_1(sK6) != sK4 ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_820,plain,
    ( k2_zfmisc_1(k1_relat_1(sK6),sK5) = k2_zfmisc_1(sK4,sK5)
    | k1_relat_1(sK6) != sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_446,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_821,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_457,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_766,plain,
    ( k2_zfmisc_1(k1_relat_1(sK6),X0) != k2_zfmisc_1(sK4,sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_949,plain,
    ( k2_zfmisc_1(k1_relat_1(sK6),sK5) != k2_zfmisc_1(sK4,sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_996,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_997,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_1434,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_13,c_820,c_821,c_949,c_997])).

cnf(c_1438,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5) ),
    inference(superposition,[status(thm)],[c_836,c_1434])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k1_funct_1(sK6,X0),sK5) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_667,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3372,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_667])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_727,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_728,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_3508,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3372,c_13,c_728,c_820,c_821,c_949,c_997])).

cnf(c_3512,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_3508])).

cnf(c_730,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_731,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3512,c_997,c_949,c_821,c_820,c_731,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.39/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.04  
% 3.39/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.04  
% 3.39/1.04  ------  iProver source info
% 3.39/1.04  
% 3.39/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.04  git: non_committed_changes: false
% 3.39/1.04  git: last_make_outside_of_git: false
% 3.39/1.04  
% 3.39/1.04  ------ 
% 3.39/1.04  ------ Parsing...
% 3.39/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.04  
% 3.39/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.39/1.04  
% 3.39/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.04  
% 3.39/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.04  ------ Proving...
% 3.39/1.04  ------ Problem Properties 
% 3.39/1.04  
% 3.39/1.04  
% 3.39/1.04  clauses                                 11
% 3.39/1.04  conjectures                             2
% 3.39/1.04  EPR                                     0
% 3.39/1.04  Horn                                    8
% 3.39/1.04  unary                                   1
% 3.39/1.04  binary                                  6
% 3.39/1.04  lits                                    26
% 3.39/1.04  lits eq                                 8
% 3.39/1.04  fd_pure                                 0
% 3.39/1.04  fd_pseudo                               0
% 3.39/1.04  fd_cond                                 3
% 3.39/1.04  fd_pseudo_cond                          0
% 3.39/1.04  AC symbols                              0
% 3.39/1.04  
% 3.39/1.04  ------ Input Options Time Limit: Unbounded
% 3.39/1.04  
% 3.39/1.04  
% 3.39/1.04  ------ 
% 3.39/1.04  Current options:
% 3.39/1.04  ------ 
% 3.39/1.04  
% 3.39/1.04  
% 3.39/1.04  
% 3.39/1.04  
% 3.39/1.04  ------ Proving...
% 3.39/1.04  
% 3.39/1.04  
% 3.39/1.04  % SZS status Theorem for theBenchmark.p
% 3.39/1.04  
% 3.39/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.04  
% 3.39/1.04  fof(f4,conjecture,(
% 3.39/1.04    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.39/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.04  
% 3.39/1.04  fof(f5,negated_conjecture,(
% 3.39/1.04    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.39/1.04    inference(negated_conjecture,[],[f4])).
% 3.39/1.04  
% 3.39/1.04  fof(f12,plain,(
% 3.39/1.04    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.39/1.04    inference(ennf_transformation,[],[f5])).
% 3.39/1.04  
% 3.39/1.04  fof(f13,plain,(
% 3.39/1.04    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.39/1.04    inference(flattening,[],[f12])).
% 3.39/1.04  
% 3.39/1.04  fof(f22,plain,(
% 3.39/1.04    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)) & ! [X3] : (r2_hidden(k1_funct_1(sK6,X3),sK5) | ~r2_hidden(X3,sK4)) & k1_relat_1(sK6) = sK4 & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 3.39/1.04    introduced(choice_axiom,[])).
% 3.39/1.04  
% 3.39/1.04  fof(f23,plain,(
% 3.39/1.04    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)) & ! [X3] : (r2_hidden(k1_funct_1(sK6,X3),sK5) | ~r2_hidden(X3,sK4)) & k1_relat_1(sK6) = sK4 & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 3.39/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f13,f22])).
% 3.39/1.04  
% 3.39/1.04  fof(f37,plain,(
% 3.39/1.04    k1_relat_1(sK6) = sK4),
% 3.39/1.04    inference(cnf_transformation,[],[f23])).
% 3.39/1.04  
% 3.39/1.04  fof(f2,axiom,(
% 3.39/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.39/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.04  
% 3.39/1.04  fof(f8,plain,(
% 3.39/1.04    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.39/1.04    inference(ennf_transformation,[],[f2])).
% 3.39/1.04  
% 3.39/1.04  fof(f9,plain,(
% 3.39/1.04    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/1.04    inference(flattening,[],[f8])).
% 3.39/1.04  
% 3.39/1.04  fof(f16,plain,(
% 3.39/1.04    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/1.04    inference(nnf_transformation,[],[f9])).
% 3.39/1.04  
% 3.39/1.04  fof(f17,plain,(
% 3.39/1.04    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/1.04    inference(rectify,[],[f16])).
% 3.39/1.04  
% 3.39/1.04  fof(f20,plain,(
% 3.39/1.04    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.39/1.04    introduced(choice_axiom,[])).
% 3.39/1.04  
% 3.39/1.04  fof(f19,plain,(
% 3.39/1.04    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.39/1.04    introduced(choice_axiom,[])).
% 3.39/1.04  
% 3.39/1.04  fof(f18,plain,(
% 3.39/1.04    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.39/1.04    introduced(choice_axiom,[])).
% 3.39/1.04  
% 3.39/1.04  fof(f21,plain,(
% 3.39/1.04    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f20,f19,f18])).
% 3.39/1.04  
% 3.39/1.04  fof(f26,plain,(
% 3.39/1.04    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.04    inference(cnf_transformation,[],[f21])).
% 3.39/1.04  
% 3.39/1.04  fof(f43,plain,(
% 3.39/1.04    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.04    inference(equality_resolution,[],[f26])).
% 3.39/1.04  
% 3.39/1.04  fof(f36,plain,(
% 3.39/1.04    v1_funct_1(sK6)),
% 3.39/1.04    inference(cnf_transformation,[],[f23])).
% 3.39/1.04  
% 3.39/1.04  fof(f35,plain,(
% 3.39/1.04    v1_relat_1(sK6)),
% 3.39/1.04    inference(cnf_transformation,[],[f23])).
% 3.39/1.04  
% 3.39/1.04  fof(f1,axiom,(
% 3.39/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.39/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.04  
% 3.39/1.04  fof(f6,plain,(
% 3.39/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.39/1.04    inference(unused_predicate_definition_removal,[],[f1])).
% 3.39/1.04  
% 3.39/1.04  fof(f7,plain,(
% 3.39/1.04    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.39/1.04    inference(ennf_transformation,[],[f6])).
% 3.39/1.04  
% 3.39/1.04  fof(f14,plain,(
% 3.39/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.39/1.04    introduced(choice_axiom,[])).
% 3.39/1.04  
% 3.39/1.04  fof(f15,plain,(
% 3.39/1.04    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.39/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).
% 3.39/1.04  
% 3.39/1.04  fof(f24,plain,(
% 3.39/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.39/1.04    inference(cnf_transformation,[],[f15])).
% 3.39/1.04  
% 3.39/1.04  fof(f27,plain,(
% 3.39/1.04    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.04    inference(cnf_transformation,[],[f21])).
% 3.39/1.04  
% 3.39/1.04  fof(f42,plain,(
% 3.39/1.04    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.04    inference(equality_resolution,[],[f27])).
% 3.39/1.04  
% 3.39/1.04  fof(f3,axiom,(
% 3.39/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.39/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.04  
% 3.39/1.04  fof(f10,plain,(
% 3.39/1.04    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.39/1.04    inference(ennf_transformation,[],[f3])).
% 3.39/1.04  
% 3.39/1.04  fof(f11,plain,(
% 3.39/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.39/1.04    inference(flattening,[],[f10])).
% 3.39/1.04  
% 3.39/1.04  fof(f33,plain,(
% 3.39/1.04    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.39/1.04    inference(cnf_transformation,[],[f11])).
% 3.39/1.04  
% 3.39/1.04  fof(f34,plain,(
% 3.39/1.04    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.39/1.04    inference(cnf_transformation,[],[f11])).
% 3.39/1.04  
% 3.39/1.04  fof(f39,plain,(
% 3.39/1.04    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)),
% 3.39/1.04    inference(cnf_transformation,[],[f23])).
% 3.39/1.04  
% 3.39/1.04  fof(f38,plain,(
% 3.39/1.04    ( ! [X3] : (r2_hidden(k1_funct_1(sK6,X3),sK5) | ~r2_hidden(X3,sK4)) )),
% 3.39/1.04    inference(cnf_transformation,[],[f23])).
% 3.39/1.04  
% 3.39/1.04  fof(f25,plain,(
% 3.39/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.39/1.04    inference(cnf_transformation,[],[f15])).
% 3.39/1.04  
% 3.39/1.04  cnf(c_13,negated_conjecture,
% 3.39/1.04      ( k1_relat_1(sK6) = sK4 ),
% 3.39/1.04      inference(cnf_transformation,[],[f37]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_7,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.39/1.04      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.39/1.04      | ~ v1_relat_1(X1)
% 3.39/1.04      | ~ v1_funct_1(X1) ),
% 3.39/1.04      inference(cnf_transformation,[],[f43]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_14,negated_conjecture,
% 3.39/1.04      ( v1_funct_1(sK6) ),
% 3.39/1.04      inference(cnf_transformation,[],[f36]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_266,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.39/1.04      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.39/1.04      | ~ v1_relat_1(X1)
% 3.39/1.04      | sK6 != X1 ),
% 3.39/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_267,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.39/1.04      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
% 3.39/1.04      | ~ v1_relat_1(sK6) ),
% 3.39/1.04      inference(unflattening,[status(thm)],[c_266]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_15,negated_conjecture,
% 3.39/1.04      ( v1_relat_1(sK6) ),
% 3.39/1.04      inference(cnf_transformation,[],[f35]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_271,plain,
% 3.39/1.04      ( r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
% 3.39/1.04      | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
% 3.39/1.04      inference(global_propositional_subsumption,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_267,c_15]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_272,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.39/1.04      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) ),
% 3.39/1.04      inference(renaming,[status(thm)],[c_271]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_663,plain,
% 3.39/1.04      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.39/1.04      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_972,plain,
% 3.39/1.04      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.39/1.04      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
% 3.39/1.04      inference(superposition,[status(thm)],[c_13,c_663]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_1,plain,
% 3.39/1.04      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.39/1.04      inference(cnf_transformation,[],[f24]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_668,plain,
% 3.39/1.04      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.39/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_6,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.39/1.04      | ~ v1_relat_1(X1)
% 3.39/1.04      | ~ v1_funct_1(X1)
% 3.39/1.04      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 3.39/1.04      inference(cnf_transformation,[],[f42]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_284,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.39/1.04      | ~ v1_relat_1(X1)
% 3.39/1.04      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 3.39/1.04      | sK6 != X1 ),
% 3.39/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_285,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.39/1.04      | ~ v1_relat_1(sK6)
% 3.39/1.04      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 3.39/1.04      inference(unflattening,[status(thm)],[c_284]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_289,plain,
% 3.39/1.04      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.39/1.04      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 3.39/1.04      inference(global_propositional_subsumption,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_285,c_15]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_662,plain,
% 3.39/1.04      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 3.39/1.04      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_836,plain,
% 3.39/1.04      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
% 3.39/1.04      inference(superposition,[status(thm)],[c_668,c_662]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_9,plain,
% 3.39/1.04      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.39/1.04      | ~ v1_relat_1(X0)
% 3.39/1.04      | ~ v1_funct_1(X0) ),
% 3.39/1.04      inference(cnf_transformation,[],[f33]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_8,plain,
% 3.39/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.39/1.04      | ~ v1_relat_1(X0)
% 3.39/1.04      | ~ v1_funct_1(X0) ),
% 3.39/1.04      inference(cnf_transformation,[],[f34]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_11,negated_conjecture,
% 3.39/1.04      ( ~ v1_funct_2(sK6,sK4,sK5)
% 3.39/1.04      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.39/1.04      | ~ v1_funct_1(sK6) ),
% 3.39/1.04      inference(cnf_transformation,[],[f39]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_87,plain,
% 3.39/1.04      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.39/1.04      | ~ v1_funct_2(sK6,sK4,sK5) ),
% 3.39/1.04      inference(global_propositional_subsumption,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_11,c_14]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_88,negated_conjecture,
% 3.39/1.04      ( ~ v1_funct_2(sK6,sK4,sK5)
% 3.39/1.04      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.39/1.04      inference(renaming,[status(thm)],[c_87]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_174,plain,
% 3.39/1.04      ( ~ v1_funct_2(sK6,sK4,sK5)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.39/1.04      | ~ v1_relat_1(X0)
% 3.39/1.04      | ~ v1_funct_1(X0)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.39/1.04      | sK6 != X0 ),
% 3.39/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_88]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_175,plain,
% 3.39/1.04      ( ~ v1_funct_2(sK6,sK4,sK5)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(sK6),X0)
% 3.39/1.04      | ~ v1_relat_1(sK6)
% 3.39/1.04      | ~ v1_funct_1(sK6)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.39/1.04      inference(unflattening,[status(thm)],[c_174]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_179,plain,
% 3.39/1.04      ( ~ v1_funct_2(sK6,sK4,sK5)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(sK6),X0)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.39/1.04      inference(global_propositional_subsumption,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_175,c_15,c_14]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_199,plain,
% 3.39/1.04      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(sK6),X2)
% 3.39/1.04      | ~ v1_relat_1(X0)
% 3.39/1.04      | ~ v1_funct_1(X0)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.39/1.04      | k1_relat_1(X0) != sK4
% 3.39/1.04      | sK5 != X1
% 3.39/1.04      | sK6 != X0 ),
% 3.39/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_179]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_200,plain,
% 3.39/1.04      ( ~ r1_tarski(k2_relat_1(sK6),X0)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(sK6),sK5)
% 3.39/1.04      | ~ v1_relat_1(sK6)
% 3.39/1.04      | ~ v1_funct_1(sK6)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.39/1.04      | k1_relat_1(sK6) != sK4 ),
% 3.39/1.04      inference(unflattening,[status(thm)],[c_199]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_204,plain,
% 3.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(sK6),sK5)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(sK6),X0) ),
% 3.39/1.04      inference(global_propositional_subsumption,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_200,c_15,c_14,c_13]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_205,plain,
% 3.39/1.04      ( ~ r1_tarski(k2_relat_1(sK6),X0)
% 3.39/1.04      | ~ r1_tarski(k2_relat_1(sK6),sK5)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.39/1.04      inference(renaming,[status(thm)],[c_204]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_666,plain,
% 3.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_205]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_456,plain,
% 3.39/1.04      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.39/1.04      theory(equality) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_800,plain,
% 3.39/1.04      ( X0 != sK5
% 3.39/1.04      | k2_zfmisc_1(k1_relat_1(sK6),X0) = k2_zfmisc_1(sK4,sK5)
% 3.39/1.04      | k1_relat_1(sK6) != sK4 ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_456]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_820,plain,
% 3.39/1.04      ( k2_zfmisc_1(k1_relat_1(sK6),sK5) = k2_zfmisc_1(sK4,sK5)
% 3.39/1.04      | k1_relat_1(sK6) != sK4
% 3.39/1.04      | sK5 != sK5 ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_800]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_446,plain,( X0 = X0 ),theory(equality) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_821,plain,
% 3.39/1.04      ( sK5 = sK5 ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_446]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_457,plain,
% 3.39/1.04      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.39/1.04      theory(equality) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_766,plain,
% 3.39/1.04      ( k2_zfmisc_1(k1_relat_1(sK6),X0) != k2_zfmisc_1(sK4,sK5)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_457]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_949,plain,
% 3.39/1.04      ( k2_zfmisc_1(k1_relat_1(sK6),sK5) != k2_zfmisc_1(sK4,sK5)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_766]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_996,plain,
% 3.39/1.04      ( ~ r1_tarski(k2_relat_1(sK6),sK5)
% 3.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_205]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_997,plain,
% 3.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_1434,plain,
% 3.39/1.04      ( r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.39/1.04      inference(global_propositional_subsumption,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_666,c_13,c_820,c_821,c_949,c_997]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_1438,plain,
% 3.39/1.04      ( k1_funct_1(sK6,sK3(sK6,sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5) ),
% 3.39/1.04      inference(superposition,[status(thm)],[c_836,c_1434]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_12,negated_conjecture,
% 3.39/1.04      ( ~ r2_hidden(X0,sK4) | r2_hidden(k1_funct_1(sK6,X0),sK5) ),
% 3.39/1.04      inference(cnf_transformation,[],[f38]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_667,plain,
% 3.39/1.04      ( r2_hidden(X0,sK4) != iProver_top
% 3.39/1.04      | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_3372,plain,
% 3.39/1.04      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top
% 3.39/1.04      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
% 3.39/1.04      inference(superposition,[status(thm)],[c_1438,c_667]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_0,plain,
% 3.39/1.04      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.39/1.04      inference(cnf_transformation,[],[f25]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_727,plain,
% 3.39/1.04      ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),sK5) ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_728,plain,
% 3.39/1.04      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_3508,plain,
% 3.39/1.04      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top ),
% 3.39/1.04      inference(global_propositional_subsumption,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_3372,c_13,c_728,c_820,c_821,c_949,c_997]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_3512,plain,
% 3.39/1.04      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top ),
% 3.39/1.04      inference(superposition,[status(thm)],[c_972,c_3508]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_730,plain,
% 3.39/1.04      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),sK5) ),
% 3.39/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(c_731,plain,
% 3.39/1.04      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top
% 3.39/1.04      | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.39/1.04      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 3.39/1.04  
% 3.39/1.04  cnf(contradiction,plain,
% 3.39/1.04      ( $false ),
% 3.39/1.04      inference(minisat,
% 3.39/1.04                [status(thm)],
% 3.39/1.04                [c_3512,c_997,c_949,c_821,c_820,c_731,c_13]) ).
% 3.39/1.04  
% 3.39/1.04  
% 3.39/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.04  
% 3.39/1.04  ------                               Statistics
% 3.39/1.04  
% 3.39/1.04  ------ Selected
% 3.39/1.04  
% 3.39/1.04  total_time:                             0.191
% 3.39/1.04  
%------------------------------------------------------------------------------
