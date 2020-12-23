%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0827+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:11 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 210 expanded)
%              Number of clauses        :   50 (  75 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  300 ( 779 expanded)
%              Number of equality atoms :  113 ( 174 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f33,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f49,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK5,k2_relset_1(sK3,sK4,sK6))
        | ~ r1_tarski(sK5,k1_relset_1(sK3,sK4,sK6)) )
      & r1_tarski(k6_relat_1(sK5),sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_tarski(sK5,k2_relset_1(sK3,sK4,sK6))
      | ~ r1_tarski(sK5,k1_relset_1(sK3,sK4,sK6)) )
    & r1_tarski(k6_relat_1(sK5),sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f28])).

fof(f46,plain,(
    r1_tarski(k6_relat_1(sK5),sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,
    ( ~ r1_tarski(sK5,k2_relset_1(sK3,sK4,sK6))
    | ~ r1_tarski(sK5,k1_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1225,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1229,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1223,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1294,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1229,c_1223])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK5),sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1219,plain,
    ( r1_tarski(k6_relat_1(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1224,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1513,plain,
    ( r2_hidden(X0,k6_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1224])).

cnf(c_1814,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1513])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1222,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1983,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1222])).

cnf(c_935,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1398,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_227,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_228,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_1401,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_1402,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1401])).

cnf(c_2353,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1983,c_1398,c_1402])).

cnf(c_2354,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2353])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1226,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2361,plain,
    ( r1_tarski(X0,k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK2(X0,k2_relat_1(sK6)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_1226])).

cnf(c_2574,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_2361])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1221,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1834,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1221])).

cnf(c_2195,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_1398,c_1402])).

cnf(c_2196,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2195])).

cnf(c_2203,plain,
    ( r1_tarski(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK2(X0,k1_relat_1(sK6)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_1226])).

cnf(c_2531,plain,
    ( r1_tarski(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_2203])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_209,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_210,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_1372,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_210])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK5,k2_relset_1(sK3,sK4,sK6))
    | ~ r1_tarski(sK5,k1_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1220,plain,
    ( r1_tarski(sK5,k2_relset_1(sK3,sK4,sK6)) != iProver_top
    | r1_tarski(sK5,k1_relset_1(sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1418,plain,
    ( r1_tarski(sK5,k1_relset_1(sK3,sK4,sK6)) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1372,c_1220])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_218,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_219,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_1391,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_219])).

cnf(c_1452,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top
    | r1_tarski(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1418,c_1391])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2574,c_2531,c_1452])).


%------------------------------------------------------------------------------
