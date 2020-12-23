%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1011+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:39 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 302 expanded)
%              Number of clauses        :   33 (  60 expanded)
%              Number of leaves         :    7 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  254 (1926 expanded)
%              Number of equality atoms :   54 (  79 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X2,X0,k1_tarski(X1))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,k1_tarski(X1),X2,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK4,X0,k1_tarski(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK1,k1_tarski(sK2),sK3,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
          & v1_funct_2(X3,sK1,k1_tarski(sK2))
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK3,sK1,k1_tarski(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r2_relset_1(sK1,k1_tarski(sK2),sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK3,sK1,k1_tarski(sK2))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f14,f13])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f7])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & r2_hidden(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
            & r2_hidden(sK0(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f11])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ~ r2_relset_1(sK1,k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    v1_funct_2(sK3,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,X3) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | r2_hidden(sK0(X0,X2,X3),X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,negated_conjecture,
    ( ~ r2_relset_1(sK1,k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_147,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | r2_hidden(sK0(X1,X3,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_tarski(sK2) != X2
    | sK4 != X0
    | sK3 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_148,plain,
    ( ~ v1_funct_2(sK4,sK1,k1_tarski(sK2))
    | ~ v1_funct_2(sK3,sK1,k1_tarski(sK2))
    | r2_hidden(sK0(sK1,sK3,sK4),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,negated_conjecture,
    ( v1_funct_2(sK3,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_150,plain,
    ( r2_hidden(sK0(sK1,sK3,sK4),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_148,c_9,c_8,c_7,c_6,c_5,c_4])).

cnf(c_169,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X0)
    | sK0(sK1,sK3,sK4) != X3
    | k1_funct_1(X0,X3) = X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_150])).

cnf(c_170,plain,
    ( ~ v1_funct_2(X0,sK1,k1_tarski(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X1))))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(sK1,sK3,sK4)) = X1 ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_213,plain,
    ( ~ v1_funct_2(X0,sK1,k1_tarski(X1))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(sK1,sK3,sK4)) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X1))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_170])).

cnf(c_214,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_tarski(X0))
    | ~ v1_funct_1(sK3)
    | k1_funct_1(sK3,sK0(sK1,sK3,sK4)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X0))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_218,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_tarski(X0))
    | k1_funct_1(sK3,sK0(sK1,sK3,sK4)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X0))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_9])).

cnf(c_533,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK3,sK4)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X0))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))
    | v1_funct_2(sK3,sK1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_616,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK3,sK4)) = sK2
    | v1_funct_2(sK3,sK1,k1_tarski(sK2)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_533])).

cnf(c_11,plain,
    ( v1_funct_2(sK3,sK1,k1_tarski(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_667,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_11])).

cnf(c_0,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_158,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
    | k1_tarski(sK2) != X2
    | sK4 != X0
    | sK3 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_159,plain,
    ( ~ v1_funct_2(sK4,sK1,k1_tarski(sK2))
    | ~ v1_funct_2(sK3,sK1,k1_tarski(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(sK4,sK0(sK1,sK3,sK4)) != k1_funct_1(sK3,sK0(sK1,sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_161,plain,
    ( k1_funct_1(sK4,sK0(sK1,sK3,sK4)) != k1_funct_1(sK3,sK0(sK1,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_159,c_9,c_8,c_7,c_6,c_5,c_4])).

cnf(c_671,plain,
    ( k1_funct_1(sK4,sK0(sK1,sK3,sK4)) != sK2 ),
    inference(demodulation,[status(thm)],[c_667,c_161])).

cnf(c_448,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_620,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) = k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_192,plain,
    ( ~ v1_funct_2(X0,sK1,k1_tarski(X1))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(sK1,sK3,sK4)) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X1))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_170])).

cnf(c_193,plain,
    ( ~ v1_funct_2(sK4,sK1,k1_tarski(X0))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK0(sK1,sK3,sK4)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X0))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_197,plain,
    ( ~ v1_funct_2(sK4,sK1,k1_tarski(X0))
    | k1_funct_1(sK4,sK0(sK1,sK3,sK4)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(X0))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_193,c_6])).

cnf(c_564,plain,
    ( ~ v1_funct_2(sK4,sK1,k1_tarski(sK2))
    | k1_funct_1(sK4,sK0(sK1,sK3,sK4)) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_671,c_620,c_564,c_5])).


%------------------------------------------------------------------------------
