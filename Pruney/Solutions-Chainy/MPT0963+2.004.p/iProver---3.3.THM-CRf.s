%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:18 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 273 expanded)
%              Number of clauses        :   44 (  77 expanded)
%              Number of leaves         :    7 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  334 (1788 expanded)
%              Number of equality atoms :  112 ( 321 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f21,plain,
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
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK3,X3),sK2)
          | ~ r2_hidden(X3,sK1) )
      & k1_relat_1(sK3) = sK1
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK3,X3),sK2)
        | ~ r2_hidden(X3,sK1) )
    & k1_relat_1(sK3) = sK1
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f21])).

fof(f36,plain,(
    k1_relat_1(sK3) = sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
                | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
                  & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK3,X3),sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_13,negated_conjecture,
    ( k1_relat_1(sK3) = sK1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_516,plain,
    ( k10_relat_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1736,plain,
    ( k10_relat_1(sK3,X0) = X1
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),sK1) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_516])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1846,plain,
    ( k10_relat_1(sK3,X0) = X1
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1736,c_16,c_17])).

cnf(c_1857,plain,
    ( k10_relat_1(sK3,X0) = sK1
    | r2_hidden(sK0(sK3,X0,sK1),sK1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1846])).

cnf(c_1859,plain,
    ( k10_relat_1(sK3,X0) = sK1
    | r2_hidden(sK0(sK3,X0,sK1),sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1857])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_509,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_518,plain,
    ( k10_relat_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2082,plain,
    ( k10_relat_1(sK3,sK2) = X0
    | r2_hidden(sK0(sK3,sK2,X0),X0) != iProver_top
    | r2_hidden(sK0(sK3,sK2,X0),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,sK2,X0),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_518])).

cnf(c_2214,plain,
    ( k10_relat_1(sK3,sK2) = X0
    | r2_hidden(sK0(sK3,sK2,X0),X0) != iProver_top
    | r2_hidden(sK0(sK3,sK2,X0),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2082,c_13])).

cnf(c_2239,plain,
    ( k10_relat_1(sK3,sK2) = X0
    | r2_hidden(sK0(sK3,sK2,X0),X0) != iProver_top
    | r2_hidden(sK0(sK3,sK2,X0),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2214,c_16,c_17])).

cnf(c_3669,plain,
    ( k10_relat_1(sK3,sK2) = sK1
    | r2_hidden(sK0(sK3,sK2,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_2239])).

cnf(c_3674,plain,
    ( k10_relat_1(sK3,sK2) = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3669,c_1859])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_512,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3954,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),sK2) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_512])).

cnf(c_507,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_519,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_748,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_507,c_519])).

cnf(c_749,plain,
    ( k9_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_748,c_13])).

cnf(c_3964,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3954,c_749])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_511,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1108,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_511])).

cnf(c_1113,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_16,c_17])).

cnf(c_11,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_110,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_14])).

cnf(c_111,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_110])).

cnf(c_506,plain,
    ( v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_111])).

cnf(c_1121,plain,
    ( v1_funct_2(sK3,sK1,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_506])).

cnf(c_9,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_510,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_921,plain,
    ( v1_funct_2(sK3,sK1,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_510])).

cnf(c_926,plain,
    ( v1_funct_2(sK3,sK1,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_16,c_17])).

cnf(c_1194,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1121,c_926])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3964,c_1194,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.58/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/1.02  
% 3.58/1.02  ------  iProver source info
% 3.58/1.02  
% 3.58/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.58/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/1.02  git: non_committed_changes: false
% 3.58/1.02  git: last_make_outside_of_git: false
% 3.58/1.02  
% 3.58/1.02  ------ 
% 3.58/1.02  ------ Parsing...
% 3.58/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  ------ Proving...
% 3.58/1.02  ------ Problem Properties 
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  clauses                                 15
% 3.58/1.02  conjectures                             5
% 3.58/1.02  EPR                                     2
% 3.58/1.02  Horn                                    13
% 3.58/1.02  unary                                   3
% 3.58/1.02  binary                                  3
% 3.58/1.02  lits                                    49
% 3.58/1.02  lits eq                                 5
% 3.58/1.02  fd_pure                                 0
% 3.58/1.02  fd_pseudo                               0
% 3.58/1.02  fd_cond                                 0
% 3.58/1.02  fd_pseudo_cond                          3
% 3.58/1.02  AC symbols                              0
% 3.58/1.02  
% 3.58/1.02  ------ Input Options Time Limit: Unbounded
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ 
% 3.58/1.02  Current options:
% 3.58/1.02  ------ 
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  % SZS status Theorem for theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  fof(f5,conjecture,(
% 3.58/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f6,negated_conjecture,(
% 3.58/1.02    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.58/1.02    inference(negated_conjecture,[],[f5])).
% 3.58/1.02  
% 3.58/1.02  fof(f14,plain,(
% 3.58/1.02    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.58/1.02    inference(ennf_transformation,[],[f6])).
% 3.58/1.02  
% 3.58/1.02  fof(f15,plain,(
% 3.58/1.02    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.58/1.02    inference(flattening,[],[f14])).
% 3.58/1.02  
% 3.58/1.02  fof(f21,plain,(
% 3.58/1.02    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) & ! [X3] : (r2_hidden(k1_funct_1(sK3,X3),sK2) | ~r2_hidden(X3,sK1)) & k1_relat_1(sK3) = sK1 & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 3.58/1.02    introduced(choice_axiom,[])).
% 3.58/1.02  
% 3.58/1.02  fof(f22,plain,(
% 3.58/1.02    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) & ! [X3] : (r2_hidden(k1_funct_1(sK3,X3),sK2) | ~r2_hidden(X3,sK1)) & k1_relat_1(sK3) = sK1 & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 3.58/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f21])).
% 3.58/1.02  
% 3.58/1.02  fof(f36,plain,(
% 3.58/1.02    k1_relat_1(sK3) = sK1),
% 3.58/1.02    inference(cnf_transformation,[],[f22])).
% 3.58/1.02  
% 3.58/1.02  fof(f2,axiom,(
% 3.58/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f8,plain,(
% 3.58/1.02    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.58/1.02    inference(ennf_transformation,[],[f2])).
% 3.58/1.02  
% 3.58/1.02  fof(f9,plain,(
% 3.58/1.02    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.02    inference(flattening,[],[f8])).
% 3.58/1.02  
% 3.58/1.02  fof(f16,plain,(
% 3.58/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.02    inference(nnf_transformation,[],[f9])).
% 3.58/1.02  
% 3.58/1.02  fof(f17,plain,(
% 3.58/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.02    inference(flattening,[],[f16])).
% 3.58/1.02  
% 3.58/1.02  fof(f18,plain,(
% 3.58/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.02    inference(rectify,[],[f17])).
% 3.58/1.02  
% 3.58/1.02  fof(f19,plain,(
% 3.58/1.02    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.58/1.02    introduced(choice_axiom,[])).
% 3.58/1.02  
% 3.58/1.02  fof(f20,plain,(
% 3.58/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.58/1.02  
% 3.58/1.02  fof(f27,plain,(
% 3.58/1.02    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f20])).
% 3.58/1.02  
% 3.58/1.02  fof(f34,plain,(
% 3.58/1.02    v1_relat_1(sK3)),
% 3.58/1.02    inference(cnf_transformation,[],[f22])).
% 3.58/1.02  
% 3.58/1.02  fof(f35,plain,(
% 3.58/1.02    v1_funct_1(sK3)),
% 3.58/1.02    inference(cnf_transformation,[],[f22])).
% 3.58/1.02  
% 3.58/1.02  fof(f37,plain,(
% 3.58/1.02    ( ! [X3] : (r2_hidden(k1_funct_1(sK3,X3),sK2) | ~r2_hidden(X3,sK1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f22])).
% 3.58/1.02  
% 3.58/1.02  fof(f29,plain,(
% 3.58/1.02    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | ~r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f20])).
% 3.58/1.02  
% 3.58/1.02  fof(f3,axiom,(
% 3.58/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f10,plain,(
% 3.58/1.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.58/1.02    inference(ennf_transformation,[],[f3])).
% 3.58/1.02  
% 3.58/1.02  fof(f11,plain,(
% 3.58/1.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.58/1.02    inference(flattening,[],[f10])).
% 3.58/1.02  
% 3.58/1.02  fof(f30,plain,(
% 3.58/1.02    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f11])).
% 3.58/1.02  
% 3.58/1.02  fof(f1,axiom,(
% 3.58/1.02    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f7,plain,(
% 3.58/1.02    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.02    inference(ennf_transformation,[],[f1])).
% 3.58/1.02  
% 3.58/1.02  fof(f23,plain,(
% 3.58/1.02    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f7])).
% 3.58/1.02  
% 3.58/1.02  fof(f4,axiom,(
% 3.58/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f12,plain,(
% 3.58/1.02    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.58/1.02    inference(ennf_transformation,[],[f4])).
% 3.58/1.02  
% 3.58/1.02  fof(f13,plain,(
% 3.58/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.58/1.02    inference(flattening,[],[f12])).
% 3.58/1.02  
% 3.58/1.02  fof(f33,plain,(
% 3.58/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f13])).
% 3.58/1.02  
% 3.58/1.02  fof(f38,plain,(
% 3.58/1.02    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 3.58/1.02    inference(cnf_transformation,[],[f22])).
% 3.58/1.02  
% 3.58/1.02  fof(f32,plain,(
% 3.58/1.02    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f13])).
% 3.58/1.02  
% 3.58/1.02  cnf(c_13,negated_conjecture,
% 3.58/1.02      ( k1_relat_1(sK3) = sK1 ),
% 3.58/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3,plain,
% 3.58/1.02      ( r2_hidden(sK0(X0,X1,X2),X2)
% 3.58/1.02      | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
% 3.58/1.02      | ~ v1_funct_1(X0)
% 3.58/1.02      | ~ v1_relat_1(X0)
% 3.58/1.02      | k10_relat_1(X0,X1) = X2 ),
% 3.58/1.02      inference(cnf_transformation,[],[f27]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_516,plain,
% 3.58/1.02      ( k10_relat_1(X0,X1) = X2
% 3.58/1.02      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.58/1.02      | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) = iProver_top
% 3.58/1.02      | v1_funct_1(X0) != iProver_top
% 3.58/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1736,plain,
% 3.58/1.02      ( k10_relat_1(sK3,X0) = X1
% 3.58/1.02      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
% 3.58/1.02      | r2_hidden(sK0(sK3,X0,X1),sK1) = iProver_top
% 3.58/1.02      | v1_funct_1(sK3) != iProver_top
% 3.58/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_13,c_516]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_15,negated_conjecture,
% 3.58/1.02      ( v1_relat_1(sK3) ),
% 3.58/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_16,plain,
% 3.58/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_14,negated_conjecture,
% 3.58/1.02      ( v1_funct_1(sK3) ),
% 3.58/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_17,plain,
% 3.58/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1846,plain,
% 3.58/1.02      ( k10_relat_1(sK3,X0) = X1
% 3.58/1.02      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
% 3.58/1.02      | r2_hidden(sK0(sK3,X0,X1),sK1) = iProver_top ),
% 3.58/1.02      inference(global_propositional_subsumption,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_1736,c_16,c_17]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1857,plain,
% 3.58/1.02      ( k10_relat_1(sK3,X0) = sK1
% 3.58/1.02      | r2_hidden(sK0(sK3,X0,sK1),sK1) = iProver_top
% 3.58/1.02      | iProver_top != iProver_top ),
% 3.58/1.02      inference(equality_factoring,[status(thm)],[c_1846]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1859,plain,
% 3.58/1.02      ( k10_relat_1(sK3,X0) = sK1
% 3.58/1.02      | r2_hidden(sK0(sK3,X0,sK1),sK1) = iProver_top ),
% 3.58/1.02      inference(equality_resolution_simp,[status(thm)],[c_1857]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_12,negated_conjecture,
% 3.58/1.02      ( ~ r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
% 3.58/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_509,plain,
% 3.58/1.02      ( r2_hidden(X0,sK1) != iProver_top
% 3.58/1.02      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1,plain,
% 3.58/1.02      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.58/1.02      | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
% 3.58/1.02      | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
% 3.58/1.02      | ~ v1_funct_1(X0)
% 3.58/1.02      | ~ v1_relat_1(X0)
% 3.58/1.02      | k10_relat_1(X0,X1) = X2 ),
% 3.58/1.02      inference(cnf_transformation,[],[f29]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_518,plain,
% 3.58/1.02      ( k10_relat_1(X0,X1) = X2
% 3.58/1.02      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 3.58/1.02      | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) != iProver_top
% 3.58/1.02      | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1) != iProver_top
% 3.58/1.02      | v1_funct_1(X0) != iProver_top
% 3.58/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2082,plain,
% 3.58/1.02      ( k10_relat_1(sK3,sK2) = X0
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,X0),X0) != iProver_top
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,X0),k1_relat_1(sK3)) != iProver_top
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,X0),sK1) != iProver_top
% 3.58/1.02      | v1_funct_1(sK3) != iProver_top
% 3.58/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_509,c_518]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2214,plain,
% 3.58/1.02      ( k10_relat_1(sK3,sK2) = X0
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,X0),X0) != iProver_top
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,X0),sK1) != iProver_top
% 3.58/1.02      | v1_funct_1(sK3) != iProver_top
% 3.58/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.02      inference(light_normalisation,[status(thm)],[c_2082,c_13]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2239,plain,
% 3.58/1.02      ( k10_relat_1(sK3,sK2) = X0
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,X0),X0) != iProver_top
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,X0),sK1) != iProver_top ),
% 3.58/1.02      inference(global_propositional_subsumption,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_2214,c_16,c_17]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3669,plain,
% 3.58/1.02      ( k10_relat_1(sK3,sK2) = sK1
% 3.58/1.02      | r2_hidden(sK0(sK3,sK2,sK1),sK1) != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_1859,c_2239]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3674,plain,
% 3.58/1.02      ( k10_relat_1(sK3,sK2) = sK1 ),
% 3.58/1.02      inference(forward_subsumption_resolution,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_3669,c_1859]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_7,plain,
% 3.58/1.02      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.58/1.02      | ~ v1_funct_1(X0)
% 3.58/1.02      | ~ v1_relat_1(X0) ),
% 3.58/1.02      inference(cnf_transformation,[],[f30]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_512,plain,
% 3.58/1.02      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 3.58/1.02      | v1_funct_1(X0) != iProver_top
% 3.58/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3954,plain,
% 3.58/1.02      ( r1_tarski(k9_relat_1(sK3,sK1),sK2) = iProver_top
% 3.58/1.02      | v1_funct_1(sK3) != iProver_top
% 3.58/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3674,c_512]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_507,plain,
% 3.58/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_0,plain,
% 3.58/1.02      ( ~ v1_relat_1(X0)
% 3.58/1.02      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.58/1.02      inference(cnf_transformation,[],[f23]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_519,plain,
% 3.58/1.02      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.58/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_748,plain,
% 3.58/1.02      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_507,c_519]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_749,plain,
% 3.58/1.02      ( k9_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 3.58/1.02      inference(light_normalisation,[status(thm)],[c_748,c_13]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3964,plain,
% 3.58/1.02      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 3.58/1.02      | v1_funct_1(sK3) != iProver_top
% 3.58/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.02      inference(light_normalisation,[status(thm)],[c_3954,c_749]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_8,plain,
% 3.58/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.58/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.58/1.02      | ~ v1_funct_1(X0)
% 3.58/1.02      | ~ v1_relat_1(X0) ),
% 3.58/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_511,plain,
% 3.58/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.58/1.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.58/1.02      | v1_funct_1(X0) != iProver_top
% 3.58/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1108,plain,
% 3.58/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.58/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.58/1.02      | v1_funct_1(sK3) != iProver_top
% 3.58/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_13,c_511]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1113,plain,
% 3.58/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.58/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.58/1.02      inference(global_propositional_subsumption,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_1108,c_16,c_17]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_11,negated_conjecture,
% 3.58/1.02      ( ~ v1_funct_2(sK3,sK1,sK2)
% 3.58/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.58/1.02      | ~ v1_funct_1(sK3) ),
% 3.58/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_110,plain,
% 3.58/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.58/1.02      | ~ v1_funct_2(sK3,sK1,sK2) ),
% 3.58/1.02      inference(global_propositional_subsumption,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_11,c_14]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_111,negated_conjecture,
% 3.58/1.02      ( ~ v1_funct_2(sK3,sK1,sK2)
% 3.58/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.58/1.02      inference(renaming,[status(thm)],[c_110]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_506,plain,
% 3.58/1.02      ( v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.58/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_111]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1121,plain,
% 3.58/1.02      ( v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.58/1.02      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_1113,c_506]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_9,plain,
% 3.58/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.58/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.58/1.02      | ~ v1_funct_1(X0)
% 3.58/1.02      | ~ v1_relat_1(X0) ),
% 3.58/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_510,plain,
% 3.58/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 3.58/1.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.58/1.02      | v1_funct_1(X0) != iProver_top
% 3.58/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_921,plain,
% 3.58/1.02      ( v1_funct_2(sK3,sK1,X0) = iProver_top
% 3.58/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.58/1.02      | v1_funct_1(sK3) != iProver_top
% 3.58/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_13,c_510]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_926,plain,
% 3.58/1.02      ( v1_funct_2(sK3,sK1,X0) = iProver_top
% 3.58/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.58/1.02      inference(global_propositional_subsumption,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_921,c_16,c_17]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1194,plain,
% 3.58/1.02      ( r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 3.58/1.02      inference(forward_subsumption_resolution,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_1121,c_926]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(contradiction,plain,
% 3.58/1.02      ( $false ),
% 3.58/1.02      inference(minisat,[status(thm)],[c_3964,c_1194,c_17,c_16]) ).
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  ------                               Statistics
% 3.58/1.02  
% 3.58/1.02  ------ Selected
% 3.58/1.02  
% 3.58/1.02  total_time:                             0.186
% 3.58/1.02  
%------------------------------------------------------------------------------
