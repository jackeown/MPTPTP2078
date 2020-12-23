%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:57 EST 2020

% Result     : Theorem 1.26s
% Output     : CNFRefutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 195 expanded)
%              Number of clauses        :   46 (  51 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  284 (1163 expanded)
%              Number of equality atoms :   54 (  54 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X3,X0,X1)
                      & v1_funct_1(X3) )
                   => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_hidden(k3_funct_2(X0,X1,sK3,X2),k2_relset_1(X0,X1,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ r2_hidden(k3_funct_2(X0,X1,X3,sK2),k2_relset_1(X0,X1,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k3_funct_2(X0,sK1,X3,X2),k2_relset_1(X0,sK1,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
                & v1_funct_2(X3,X0,sK1)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,X0) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
                  & v1_funct_2(X3,sK0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,sK0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,sK0)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38,f37,f36,f35])).

fof(f58,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_393,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_953,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_394,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_829,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_952,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_954,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_644,plain,
    ( m1_subset_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK1 != X3
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,sK0)
    | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_22,c_19,c_17])).

cnf(c_638,plain,
    ( k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_882,plain,
    ( k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_644,c_638])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_646,plain,
    ( r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_884,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_882,c_646])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | sK3 != X2
    | sK1 != X3
    | sK0 != X1
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_254,plain,
    ( ~ r2_hidden(X0,sK0)
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_258,plain,
    ( ~ r2_hidden(X0,sK0)
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_19,c_17])).

cnf(c_876,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_877,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) = iProver_top
    | r2_hidden(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_785,plain,
    ( r2_hidden(X0,sK0)
    | ~ m1_subset_1(X0,sK0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_832,plain,
    ( r2_hidden(sK2,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_833,plain,
    ( r2_hidden(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_395,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_765,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_767,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_61,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_58,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_53,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_46,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_953,c_954,c_884,c_877,c_833,c_767,c_61,c_58,c_53,c_46,c_25,c_21,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:01:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 1.26/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.26/0.97  
% 1.26/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.26/0.97  
% 1.26/0.97  ------  iProver source info
% 1.26/0.97  
% 1.26/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.26/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.26/0.97  git: non_committed_changes: false
% 1.26/0.97  git: last_make_outside_of_git: false
% 1.26/0.97  
% 1.26/0.97  ------ 
% 1.26/0.97  
% 1.26/0.97  ------ Input Options
% 1.26/0.97  
% 1.26/0.97  --out_options                           all
% 1.26/0.97  --tptp_safe_out                         true
% 1.26/0.97  --problem_path                          ""
% 1.26/0.97  --include_path                          ""
% 1.26/0.97  --clausifier                            res/vclausify_rel
% 1.26/0.97  --clausifier_options                    --mode clausify
% 1.26/0.97  --stdin                                 false
% 1.26/0.97  --stats_out                             all
% 1.26/0.97  
% 1.26/0.97  ------ General Options
% 1.26/0.97  
% 1.26/0.97  --fof                                   false
% 1.26/0.97  --time_out_real                         305.
% 1.26/0.97  --time_out_virtual                      -1.
% 1.26/0.97  --symbol_type_check                     false
% 1.26/0.97  --clausify_out                          false
% 1.26/0.97  --sig_cnt_out                           false
% 1.26/0.97  --trig_cnt_out                          false
% 1.26/0.97  --trig_cnt_out_tolerance                1.
% 1.26/0.97  --trig_cnt_out_sk_spl                   false
% 1.26/0.97  --abstr_cl_out                          false
% 1.26/0.97  
% 1.26/0.97  ------ Global Options
% 1.26/0.97  
% 1.26/0.97  --schedule                              default
% 1.26/0.97  --add_important_lit                     false
% 1.26/0.97  --prop_solver_per_cl                    1000
% 1.26/0.97  --min_unsat_core                        false
% 1.26/0.97  --soft_assumptions                      false
% 1.26/0.97  --soft_lemma_size                       3
% 1.26/0.97  --prop_impl_unit_size                   0
% 1.26/0.97  --prop_impl_unit                        []
% 1.26/0.97  --share_sel_clauses                     true
% 1.26/0.97  --reset_solvers                         false
% 1.26/0.97  --bc_imp_inh                            [conj_cone]
% 1.26/0.97  --conj_cone_tolerance                   3.
% 1.26/0.97  --extra_neg_conj                        none
% 1.26/0.97  --large_theory_mode                     true
% 1.26/0.97  --prolific_symb_bound                   200
% 1.26/0.97  --lt_threshold                          2000
% 1.26/0.97  --clause_weak_htbl                      true
% 1.26/0.97  --gc_record_bc_elim                     false
% 1.26/0.97  
% 1.26/0.97  ------ Preprocessing Options
% 1.26/0.97  
% 1.26/0.97  --preprocessing_flag                    true
% 1.26/0.97  --time_out_prep_mult                    0.1
% 1.26/0.97  --splitting_mode                        input
% 1.26/0.97  --splitting_grd                         true
% 1.26/0.97  --splitting_cvd                         false
% 1.26/0.97  --splitting_cvd_svl                     false
% 1.26/0.97  --splitting_nvd                         32
% 1.26/0.97  --sub_typing                            true
% 1.26/0.97  --prep_gs_sim                           true
% 1.26/0.97  --prep_unflatten                        true
% 1.26/0.97  --prep_res_sim                          true
% 1.26/0.97  --prep_upred                            true
% 1.26/0.97  --prep_sem_filter                       exhaustive
% 1.26/0.97  --prep_sem_filter_out                   false
% 1.26/0.97  --pred_elim                             true
% 1.26/0.97  --res_sim_input                         true
% 1.26/0.97  --eq_ax_congr_red                       true
% 1.26/0.97  --pure_diseq_elim                       true
% 1.26/0.97  --brand_transform                       false
% 1.26/0.97  --non_eq_to_eq                          false
% 1.26/0.97  --prep_def_merge                        true
% 1.26/0.97  --prep_def_merge_prop_impl              false
% 1.26/0.98  --prep_def_merge_mbd                    true
% 1.26/0.98  --prep_def_merge_tr_red                 false
% 1.26/0.98  --prep_def_merge_tr_cl                  false
% 1.26/0.98  --smt_preprocessing                     true
% 1.26/0.98  --smt_ac_axioms                         fast
% 1.26/0.98  --preprocessed_out                      false
% 1.26/0.98  --preprocessed_stats                    false
% 1.26/0.98  
% 1.26/0.98  ------ Abstraction refinement Options
% 1.26/0.98  
% 1.26/0.98  --abstr_ref                             []
% 1.26/0.98  --abstr_ref_prep                        false
% 1.26/0.98  --abstr_ref_until_sat                   false
% 1.26/0.98  --abstr_ref_sig_restrict                funpre
% 1.26/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.26/0.98  --abstr_ref_under                       []
% 1.26/0.98  
% 1.26/0.98  ------ SAT Options
% 1.26/0.98  
% 1.26/0.98  --sat_mode                              false
% 1.26/0.98  --sat_fm_restart_options                ""
% 1.26/0.98  --sat_gr_def                            false
% 1.26/0.98  --sat_epr_types                         true
% 1.26/0.98  --sat_non_cyclic_types                  false
% 1.26/0.98  --sat_finite_models                     false
% 1.26/0.98  --sat_fm_lemmas                         false
% 1.26/0.98  --sat_fm_prep                           false
% 1.26/0.98  --sat_fm_uc_incr                        true
% 1.26/0.98  --sat_out_model                         small
% 1.26/0.98  --sat_out_clauses                       false
% 1.26/0.98  
% 1.26/0.98  ------ QBF Options
% 1.26/0.98  
% 1.26/0.98  --qbf_mode                              false
% 1.26/0.98  --qbf_elim_univ                         false
% 1.26/0.98  --qbf_dom_inst                          none
% 1.26/0.98  --qbf_dom_pre_inst                      false
% 1.26/0.98  --qbf_sk_in                             false
% 1.26/0.98  --qbf_pred_elim                         true
% 1.26/0.98  --qbf_split                             512
% 1.26/0.98  
% 1.26/0.98  ------ BMC1 Options
% 1.26/0.98  
% 1.26/0.98  --bmc1_incremental                      false
% 1.26/0.98  --bmc1_axioms                           reachable_all
% 1.26/0.98  --bmc1_min_bound                        0
% 1.26/0.98  --bmc1_max_bound                        -1
% 1.26/0.98  --bmc1_max_bound_default                -1
% 1.26/0.98  --bmc1_symbol_reachability              true
% 1.26/0.98  --bmc1_property_lemmas                  false
% 1.26/0.98  --bmc1_k_induction                      false
% 1.26/0.98  --bmc1_non_equiv_states                 false
% 1.26/0.98  --bmc1_deadlock                         false
% 1.26/0.98  --bmc1_ucm                              false
% 1.26/0.98  --bmc1_add_unsat_core                   none
% 1.26/0.98  --bmc1_unsat_core_children              false
% 1.26/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.26/0.98  --bmc1_out_stat                         full
% 1.26/0.98  --bmc1_ground_init                      false
% 1.26/0.98  --bmc1_pre_inst_next_state              false
% 1.26/0.98  --bmc1_pre_inst_state                   false
% 1.26/0.98  --bmc1_pre_inst_reach_state             false
% 1.26/0.98  --bmc1_out_unsat_core                   false
% 1.26/0.98  --bmc1_aig_witness_out                  false
% 1.26/0.98  --bmc1_verbose                          false
% 1.26/0.98  --bmc1_dump_clauses_tptp                false
% 1.26/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.26/0.98  --bmc1_dump_file                        -
% 1.26/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.26/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.26/0.98  --bmc1_ucm_extend_mode                  1
% 1.26/0.98  --bmc1_ucm_init_mode                    2
% 1.26/0.98  --bmc1_ucm_cone_mode                    none
% 1.26/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.26/0.98  --bmc1_ucm_relax_model                  4
% 1.26/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.26/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.26/0.98  --bmc1_ucm_layered_model                none
% 1.26/0.98  --bmc1_ucm_max_lemma_size               10
% 1.26/0.98  
% 1.26/0.98  ------ AIG Options
% 1.26/0.98  
% 1.26/0.98  --aig_mode                              false
% 1.26/0.98  
% 1.26/0.98  ------ Instantiation Options
% 1.26/0.98  
% 1.26/0.98  --instantiation_flag                    true
% 1.26/0.98  --inst_sos_flag                         false
% 1.26/0.98  --inst_sos_phase                        true
% 1.26/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel_side                     num_symb
% 1.26/0.98  --inst_solver_per_active                1400
% 1.26/0.98  --inst_solver_calls_frac                1.
% 1.26/0.98  --inst_passive_queue_type               priority_queues
% 1.26/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.26/0.98  --inst_passive_queues_freq              [25;2]
% 1.26/0.98  --inst_dismatching                      true
% 1.26/0.98  --inst_eager_unprocessed_to_passive     true
% 1.26/0.98  --inst_prop_sim_given                   true
% 1.26/0.98  --inst_prop_sim_new                     false
% 1.26/0.98  --inst_subs_new                         false
% 1.26/0.98  --inst_eq_res_simp                      false
% 1.26/0.98  --inst_subs_given                       false
% 1.26/0.98  --inst_orphan_elimination               true
% 1.26/0.98  --inst_learning_loop_flag               true
% 1.26/0.98  --inst_learning_start                   3000
% 1.26/0.98  --inst_learning_factor                  2
% 1.26/0.98  --inst_start_prop_sim_after_learn       3
% 1.26/0.98  --inst_sel_renew                        solver
% 1.26/0.98  --inst_lit_activity_flag                true
% 1.26/0.98  --inst_restr_to_given                   false
% 1.26/0.98  --inst_activity_threshold               500
% 1.26/0.98  --inst_out_proof                        true
% 1.26/0.98  
% 1.26/0.98  ------ Resolution Options
% 1.26/0.98  
% 1.26/0.98  --resolution_flag                       true
% 1.26/0.98  --res_lit_sel                           adaptive
% 1.26/0.98  --res_lit_sel_side                      none
% 1.26/0.98  --res_ordering                          kbo
% 1.26/0.98  --res_to_prop_solver                    active
% 1.26/0.98  --res_prop_simpl_new                    false
% 1.26/0.98  --res_prop_simpl_given                  true
% 1.26/0.98  --res_passive_queue_type                priority_queues
% 1.26/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.26/0.98  --res_passive_queues_freq               [15;5]
% 1.26/0.98  --res_forward_subs                      full
% 1.26/0.98  --res_backward_subs                     full
% 1.26/0.98  --res_forward_subs_resolution           true
% 1.26/0.98  --res_backward_subs_resolution          true
% 1.26/0.98  --res_orphan_elimination                true
% 1.26/0.98  --res_time_limit                        2.
% 1.26/0.98  --res_out_proof                         true
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Options
% 1.26/0.98  
% 1.26/0.98  --superposition_flag                    true
% 1.26/0.98  --sup_passive_queue_type                priority_queues
% 1.26/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.26/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.26/0.98  --demod_completeness_check              fast
% 1.26/0.98  --demod_use_ground                      true
% 1.26/0.98  --sup_to_prop_solver                    passive
% 1.26/0.98  --sup_prop_simpl_new                    true
% 1.26/0.98  --sup_prop_simpl_given                  true
% 1.26/0.98  --sup_fun_splitting                     false
% 1.26/0.98  --sup_smt_interval                      50000
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Simplification Setup
% 1.26/0.98  
% 1.26/0.98  --sup_indices_passive                   []
% 1.26/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.26/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_full_bw                           [BwDemod]
% 1.26/0.98  --sup_immed_triv                        [TrivRules]
% 1.26/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.26/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_immed_bw_main                     []
% 1.26/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.26/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  
% 1.26/0.98  ------ Combination Options
% 1.26/0.98  
% 1.26/0.98  --comb_res_mult                         3
% 1.26/0.98  --comb_sup_mult                         2
% 1.26/0.98  --comb_inst_mult                        10
% 1.26/0.98  
% 1.26/0.98  ------ Debug Options
% 1.26/0.98  
% 1.26/0.98  --dbg_backtrace                         false
% 1.26/0.98  --dbg_dump_prop_clauses                 false
% 1.26/0.98  --dbg_dump_prop_clauses_file            -
% 1.26/0.98  --dbg_out_stat                          false
% 1.26/0.98  ------ Parsing...
% 1.26/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.26/0.98  ------ Proving...
% 1.26/0.98  ------ Problem Properties 
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  clauses                                 16
% 1.26/0.98  conjectures                             5
% 1.26/0.98  EPR                                     5
% 1.26/0.98  Horn                                    13
% 1.26/0.98  unary                                   9
% 1.26/0.98  binary                                  2
% 1.26/0.98  lits                                    28
% 1.26/0.98  lits eq                                 7
% 1.26/0.98  fd_pure                                 0
% 1.26/0.98  fd_pseudo                               0
% 1.26/0.98  fd_cond                                 1
% 1.26/0.98  fd_pseudo_cond                          0
% 1.26/0.98  AC symbols                              0
% 1.26/0.98  
% 1.26/0.98  ------ Schedule dynamic 5 is on 
% 1.26/0.98  
% 1.26/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  ------ 
% 1.26/0.98  Current options:
% 1.26/0.98  ------ 
% 1.26/0.98  
% 1.26/0.98  ------ Input Options
% 1.26/0.98  
% 1.26/0.98  --out_options                           all
% 1.26/0.98  --tptp_safe_out                         true
% 1.26/0.98  --problem_path                          ""
% 1.26/0.98  --include_path                          ""
% 1.26/0.98  --clausifier                            res/vclausify_rel
% 1.26/0.98  --clausifier_options                    --mode clausify
% 1.26/0.98  --stdin                                 false
% 1.26/0.98  --stats_out                             all
% 1.26/0.98  
% 1.26/0.98  ------ General Options
% 1.26/0.98  
% 1.26/0.98  --fof                                   false
% 1.26/0.98  --time_out_real                         305.
% 1.26/0.98  --time_out_virtual                      -1.
% 1.26/0.98  --symbol_type_check                     false
% 1.26/0.98  --clausify_out                          false
% 1.26/0.98  --sig_cnt_out                           false
% 1.26/0.98  --trig_cnt_out                          false
% 1.26/0.98  --trig_cnt_out_tolerance                1.
% 1.26/0.98  --trig_cnt_out_sk_spl                   false
% 1.26/0.98  --abstr_cl_out                          false
% 1.26/0.98  
% 1.26/0.98  ------ Global Options
% 1.26/0.98  
% 1.26/0.98  --schedule                              default
% 1.26/0.98  --add_important_lit                     false
% 1.26/0.98  --prop_solver_per_cl                    1000
% 1.26/0.98  --min_unsat_core                        false
% 1.26/0.98  --soft_assumptions                      false
% 1.26/0.98  --soft_lemma_size                       3
% 1.26/0.98  --prop_impl_unit_size                   0
% 1.26/0.98  --prop_impl_unit                        []
% 1.26/0.98  --share_sel_clauses                     true
% 1.26/0.98  --reset_solvers                         false
% 1.26/0.98  --bc_imp_inh                            [conj_cone]
% 1.26/0.98  --conj_cone_tolerance                   3.
% 1.26/0.98  --extra_neg_conj                        none
% 1.26/0.98  --large_theory_mode                     true
% 1.26/0.98  --prolific_symb_bound                   200
% 1.26/0.98  --lt_threshold                          2000
% 1.26/0.98  --clause_weak_htbl                      true
% 1.26/0.98  --gc_record_bc_elim                     false
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing Options
% 1.26/0.98  
% 1.26/0.98  --preprocessing_flag                    true
% 1.26/0.98  --time_out_prep_mult                    0.1
% 1.26/0.98  --splitting_mode                        input
% 1.26/0.98  --splitting_grd                         true
% 1.26/0.98  --splitting_cvd                         false
% 1.26/0.98  --splitting_cvd_svl                     false
% 1.26/0.98  --splitting_nvd                         32
% 1.26/0.98  --sub_typing                            true
% 1.26/0.98  --prep_gs_sim                           true
% 1.26/0.98  --prep_unflatten                        true
% 1.26/0.98  --prep_res_sim                          true
% 1.26/0.98  --prep_upred                            true
% 1.26/0.98  --prep_sem_filter                       exhaustive
% 1.26/0.98  --prep_sem_filter_out                   false
% 1.26/0.98  --pred_elim                             true
% 1.26/0.98  --res_sim_input                         true
% 1.26/0.98  --eq_ax_congr_red                       true
% 1.26/0.98  --pure_diseq_elim                       true
% 1.26/0.98  --brand_transform                       false
% 1.26/0.98  --non_eq_to_eq                          false
% 1.26/0.98  --prep_def_merge                        true
% 1.26/0.98  --prep_def_merge_prop_impl              false
% 1.26/0.98  --prep_def_merge_mbd                    true
% 1.26/0.98  --prep_def_merge_tr_red                 false
% 1.26/0.98  --prep_def_merge_tr_cl                  false
% 1.26/0.98  --smt_preprocessing                     true
% 1.26/0.98  --smt_ac_axioms                         fast
% 1.26/0.98  --preprocessed_out                      false
% 1.26/0.98  --preprocessed_stats                    false
% 1.26/0.98  
% 1.26/0.98  ------ Abstraction refinement Options
% 1.26/0.98  
% 1.26/0.98  --abstr_ref                             []
% 1.26/0.98  --abstr_ref_prep                        false
% 1.26/0.98  --abstr_ref_until_sat                   false
% 1.26/0.98  --abstr_ref_sig_restrict                funpre
% 1.26/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.26/0.98  --abstr_ref_under                       []
% 1.26/0.98  
% 1.26/0.98  ------ SAT Options
% 1.26/0.98  
% 1.26/0.98  --sat_mode                              false
% 1.26/0.98  --sat_fm_restart_options                ""
% 1.26/0.98  --sat_gr_def                            false
% 1.26/0.98  --sat_epr_types                         true
% 1.26/0.98  --sat_non_cyclic_types                  false
% 1.26/0.98  --sat_finite_models                     false
% 1.26/0.98  --sat_fm_lemmas                         false
% 1.26/0.98  --sat_fm_prep                           false
% 1.26/0.98  --sat_fm_uc_incr                        true
% 1.26/0.98  --sat_out_model                         small
% 1.26/0.98  --sat_out_clauses                       false
% 1.26/0.98  
% 1.26/0.98  ------ QBF Options
% 1.26/0.98  
% 1.26/0.98  --qbf_mode                              false
% 1.26/0.98  --qbf_elim_univ                         false
% 1.26/0.98  --qbf_dom_inst                          none
% 1.26/0.98  --qbf_dom_pre_inst                      false
% 1.26/0.98  --qbf_sk_in                             false
% 1.26/0.98  --qbf_pred_elim                         true
% 1.26/0.98  --qbf_split                             512
% 1.26/0.98  
% 1.26/0.98  ------ BMC1 Options
% 1.26/0.98  
% 1.26/0.98  --bmc1_incremental                      false
% 1.26/0.98  --bmc1_axioms                           reachable_all
% 1.26/0.98  --bmc1_min_bound                        0
% 1.26/0.98  --bmc1_max_bound                        -1
% 1.26/0.98  --bmc1_max_bound_default                -1
% 1.26/0.98  --bmc1_symbol_reachability              true
% 1.26/0.98  --bmc1_property_lemmas                  false
% 1.26/0.98  --bmc1_k_induction                      false
% 1.26/0.98  --bmc1_non_equiv_states                 false
% 1.26/0.98  --bmc1_deadlock                         false
% 1.26/0.98  --bmc1_ucm                              false
% 1.26/0.98  --bmc1_add_unsat_core                   none
% 1.26/0.98  --bmc1_unsat_core_children              false
% 1.26/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.26/0.98  --bmc1_out_stat                         full
% 1.26/0.98  --bmc1_ground_init                      false
% 1.26/0.98  --bmc1_pre_inst_next_state              false
% 1.26/0.98  --bmc1_pre_inst_state                   false
% 1.26/0.98  --bmc1_pre_inst_reach_state             false
% 1.26/0.98  --bmc1_out_unsat_core                   false
% 1.26/0.98  --bmc1_aig_witness_out                  false
% 1.26/0.98  --bmc1_verbose                          false
% 1.26/0.98  --bmc1_dump_clauses_tptp                false
% 1.26/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.26/0.98  --bmc1_dump_file                        -
% 1.26/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.26/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.26/0.98  --bmc1_ucm_extend_mode                  1
% 1.26/0.98  --bmc1_ucm_init_mode                    2
% 1.26/0.98  --bmc1_ucm_cone_mode                    none
% 1.26/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.26/0.98  --bmc1_ucm_relax_model                  4
% 1.26/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.26/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.26/0.98  --bmc1_ucm_layered_model                none
% 1.26/0.98  --bmc1_ucm_max_lemma_size               10
% 1.26/0.98  
% 1.26/0.98  ------ AIG Options
% 1.26/0.98  
% 1.26/0.98  --aig_mode                              false
% 1.26/0.98  
% 1.26/0.98  ------ Instantiation Options
% 1.26/0.98  
% 1.26/0.98  --instantiation_flag                    true
% 1.26/0.98  --inst_sos_flag                         false
% 1.26/0.98  --inst_sos_phase                        true
% 1.26/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel_side                     none
% 1.26/0.98  --inst_solver_per_active                1400
% 1.26/0.98  --inst_solver_calls_frac                1.
% 1.26/0.98  --inst_passive_queue_type               priority_queues
% 1.26/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.26/0.98  --inst_passive_queues_freq              [25;2]
% 1.26/0.98  --inst_dismatching                      true
% 1.26/0.98  --inst_eager_unprocessed_to_passive     true
% 1.26/0.98  --inst_prop_sim_given                   true
% 1.26/0.98  --inst_prop_sim_new                     false
% 1.26/0.98  --inst_subs_new                         false
% 1.26/0.98  --inst_eq_res_simp                      false
% 1.26/0.98  --inst_subs_given                       false
% 1.26/0.98  --inst_orphan_elimination               true
% 1.26/0.98  --inst_learning_loop_flag               true
% 1.26/0.98  --inst_learning_start                   3000
% 1.26/0.98  --inst_learning_factor                  2
% 1.26/0.98  --inst_start_prop_sim_after_learn       3
% 1.26/0.98  --inst_sel_renew                        solver
% 1.26/0.98  --inst_lit_activity_flag                true
% 1.26/0.98  --inst_restr_to_given                   false
% 1.26/0.98  --inst_activity_threshold               500
% 1.26/0.98  --inst_out_proof                        true
% 1.26/0.98  
% 1.26/0.98  ------ Resolution Options
% 1.26/0.98  
% 1.26/0.98  --resolution_flag                       false
% 1.26/0.98  --res_lit_sel                           adaptive
% 1.26/0.98  --res_lit_sel_side                      none
% 1.26/0.98  --res_ordering                          kbo
% 1.26/0.98  --res_to_prop_solver                    active
% 1.26/0.98  --res_prop_simpl_new                    false
% 1.26/0.98  --res_prop_simpl_given                  true
% 1.26/0.98  --res_passive_queue_type                priority_queues
% 1.26/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.26/0.98  --res_passive_queues_freq               [15;5]
% 1.26/0.98  --res_forward_subs                      full
% 1.26/0.98  --res_backward_subs                     full
% 1.26/0.98  --res_forward_subs_resolution           true
% 1.26/0.98  --res_backward_subs_resolution          true
% 1.26/0.98  --res_orphan_elimination                true
% 1.26/0.98  --res_time_limit                        2.
% 1.26/0.98  --res_out_proof                         true
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Options
% 1.26/0.98  
% 1.26/0.98  --superposition_flag                    true
% 1.26/0.98  --sup_passive_queue_type                priority_queues
% 1.26/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.26/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.26/0.98  --demod_completeness_check              fast
% 1.26/0.98  --demod_use_ground                      true
% 1.26/0.98  --sup_to_prop_solver                    passive
% 1.26/0.98  --sup_prop_simpl_new                    true
% 1.26/0.98  --sup_prop_simpl_given                  true
% 1.26/0.98  --sup_fun_splitting                     false
% 1.26/0.98  --sup_smt_interval                      50000
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Simplification Setup
% 1.26/0.98  
% 1.26/0.98  --sup_indices_passive                   []
% 1.26/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.26/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_full_bw                           [BwDemod]
% 1.26/0.98  --sup_immed_triv                        [TrivRules]
% 1.26/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.26/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_immed_bw_main                     []
% 1.26/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.26/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  
% 1.26/0.98  ------ Combination Options
% 1.26/0.98  
% 1.26/0.98  --comb_res_mult                         3
% 1.26/0.98  --comb_sup_mult                         2
% 1.26/0.98  --comb_inst_mult                        10
% 1.26/0.98  
% 1.26/0.98  ------ Debug Options
% 1.26/0.98  
% 1.26/0.98  --dbg_backtrace                         false
% 1.26/0.98  --dbg_dump_prop_clauses                 false
% 1.26/0.98  --dbg_dump_prop_clauses_file            -
% 1.26/0.98  --dbg_out_stat                          false
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  ------ Proving...
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  % SZS status Theorem for theBenchmark.p
% 1.26/0.98  
% 1.26/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.26/0.98  
% 1.26/0.98  fof(f13,conjecture,(
% 1.26/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f14,negated_conjecture,(
% 1.26/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 1.26/0.98    inference(negated_conjecture,[],[f13])).
% 1.26/0.98  
% 1.26/0.98  fof(f31,plain,(
% 1.26/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.26/0.98    inference(ennf_transformation,[],[f14])).
% 1.26/0.98  
% 1.26/0.98  fof(f32,plain,(
% 1.26/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.26/0.98    inference(flattening,[],[f31])).
% 1.26/0.98  
% 1.26/0.98  fof(f38,plain,(
% 1.26/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k3_funct_2(X0,X1,sK3,X2),k2_relset_1(X0,X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f37,plain,(
% 1.26/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) => (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,sK2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(sK2,X0))) )),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f36,plain,(
% 1.26/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,sK1,X3,X2),k2_relset_1(X0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X3,X0,sK1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(sK1))) )),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f35,plain,(
% 1.26/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X3,sK0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f39,plain,(
% 1.26/0.98    (((~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,sK0)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38,f37,f36,f35])).
% 1.26/0.98  
% 1.26/0.98  fof(f58,plain,(
% 1.26/0.98    m1_subset_1(sK2,sK0)),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  fof(f11,axiom,(
% 1.26/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f27,plain,(
% 1.26/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.26/0.98    inference(ennf_transformation,[],[f11])).
% 1.26/0.98  
% 1.26/0.98  fof(f28,plain,(
% 1.26/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.26/0.98    inference(flattening,[],[f27])).
% 1.26/0.98  
% 1.26/0.98  fof(f54,plain,(
% 1.26/0.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f28])).
% 1.26/0.98  
% 1.26/0.98  fof(f60,plain,(
% 1.26/0.98    v1_funct_2(sK3,sK0,sK1)),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  fof(f56,plain,(
% 1.26/0.98    ~v1_xboole_0(sK0)),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  fof(f59,plain,(
% 1.26/0.98    v1_funct_1(sK3)),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  fof(f61,plain,(
% 1.26/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  fof(f62,plain,(
% 1.26/0.98    ~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  fof(f12,axiom,(
% 1.26/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f29,plain,(
% 1.26/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.26/0.98    inference(ennf_transformation,[],[f12])).
% 1.26/0.98  
% 1.26/0.98  fof(f30,plain,(
% 1.26/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.26/0.98    inference(flattening,[],[f29])).
% 1.26/0.98  
% 1.26/0.98  fof(f55,plain,(
% 1.26/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f30])).
% 1.26/0.98  
% 1.26/0.98  fof(f6,axiom,(
% 1.26/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f19,plain,(
% 1.26/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.26/0.98    inference(ennf_transformation,[],[f6])).
% 1.26/0.98  
% 1.26/0.98  fof(f20,plain,(
% 1.26/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.26/0.98    inference(flattening,[],[f19])).
% 1.26/0.98  
% 1.26/0.98  fof(f47,plain,(
% 1.26/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f20])).
% 1.26/0.98  
% 1.26/0.98  fof(f1,axiom,(
% 1.26/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f40,plain,(
% 1.26/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f1])).
% 1.26/0.98  
% 1.26/0.98  fof(f2,axiom,(
% 1.26/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f16,plain,(
% 1.26/0.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.26/0.98    inference(ennf_transformation,[],[f2])).
% 1.26/0.98  
% 1.26/0.98  fof(f17,plain,(
% 1.26/0.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.26/0.98    inference(flattening,[],[f16])).
% 1.26/0.98  
% 1.26/0.98  fof(f41,plain,(
% 1.26/0.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f17])).
% 1.26/0.98  
% 1.26/0.98  fof(f4,axiom,(
% 1.26/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f45,plain,(
% 1.26/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.26/0.98    inference(cnf_transformation,[],[f4])).
% 1.26/0.98  
% 1.26/0.98  fof(f7,axiom,(
% 1.26/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.26/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f15,plain,(
% 1.26/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.26/0.98    inference(unused_predicate_definition_removal,[],[f7])).
% 1.26/0.98  
% 1.26/0.98  fof(f21,plain,(
% 1.26/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.26/0.98    inference(ennf_transformation,[],[f15])).
% 1.26/0.98  
% 1.26/0.98  fof(f48,plain,(
% 1.26/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.26/0.98    inference(cnf_transformation,[],[f21])).
% 1.26/0.98  
% 1.26/0.98  fof(f57,plain,(
% 1.26/0.98    ~v1_xboole_0(sK1)),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  cnf(c_393,plain,( X0 = X0 ),theory(equality) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_953,plain,
% 1.26/0.98      ( sK1 = sK1 ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_393]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_394,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_829,plain,
% 1.26/0.98      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_394]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_952,plain,
% 1.26/0.98      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_829]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_954,plain,
% 1.26/0.98      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_952]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_20,negated_conjecture,
% 1.26/0.98      ( m1_subset_1(sK2,sK0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_644,plain,
% 1.26/0.98      ( m1_subset_1(sK2,sK0) = iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_14,plain,
% 1.26/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.26/0.98      | ~ m1_subset_1(X3,X1)
% 1.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.26/0.98      | ~ v1_funct_1(X0)
% 1.26/0.98      | v1_xboole_0(X1)
% 1.26/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.26/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_18,negated_conjecture,
% 1.26/0.98      ( v1_funct_2(sK3,sK0,sK1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_274,plain,
% 1.26/0.98      ( ~ m1_subset_1(X0,X1)
% 1.26/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.26/0.98      | ~ v1_funct_1(X2)
% 1.26/0.98      | v1_xboole_0(X1)
% 1.26/0.98      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.26/0.98      | sK3 != X2
% 1.26/0.98      | sK1 != X3
% 1.26/0.98      | sK0 != X1 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_275,plain,
% 1.26/0.98      ( ~ m1_subset_1(X0,sK0)
% 1.26/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.26/0.98      | ~ v1_funct_1(sK3)
% 1.26/0.98      | v1_xboole_0(sK0)
% 1.26/0.98      | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_274]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_22,negated_conjecture,
% 1.26/0.98      ( ~ v1_xboole_0(sK0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_19,negated_conjecture,
% 1.26/0.98      ( v1_funct_1(sK3) ),
% 1.26/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_17,negated_conjecture,
% 1.26/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.26/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_279,plain,
% 1.26/0.98      ( ~ m1_subset_1(X0,sK0)
% 1.26/0.98      | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_275,c_22,c_19,c_17]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_638,plain,
% 1.26/0.98      ( k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0)
% 1.26/0.98      | m1_subset_1(X0,sK0) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_882,plain,
% 1.26/0.98      ( k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_644,c_638]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_16,negated_conjecture,
% 1.26/0.98      ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
% 1.26/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_646,plain,
% 1.26/0.98      ( r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_884,plain,
% 1.26/0.98      ( r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 1.26/0.98      inference(demodulation,[status(thm)],[c_882,c_646]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_15,plain,
% 1.26/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.26/0.98      | ~ r2_hidden(X3,X1)
% 1.26/0.98      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.26/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.26/0.98      | ~ v1_funct_1(X0)
% 1.26/0.98      | k1_xboole_0 = X2 ),
% 1.26/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_253,plain,
% 1.26/0.98      ( ~ r2_hidden(X0,X1)
% 1.26/0.98      | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
% 1.26/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.26/0.98      | ~ v1_funct_1(X2)
% 1.26/0.98      | sK3 != X2
% 1.26/0.98      | sK1 != X3
% 1.26/0.98      | sK0 != X1
% 1.26/0.98      | k1_xboole_0 = X3 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_254,plain,
% 1.26/0.98      ( ~ r2_hidden(X0,sK0)
% 1.26/0.98      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))
% 1.26/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.26/0.98      | ~ v1_funct_1(sK3)
% 1.26/0.98      | k1_xboole_0 = sK1 ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_253]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_258,plain,
% 1.26/0.98      ( ~ r2_hidden(X0,sK0)
% 1.26/0.98      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))
% 1.26/0.98      | k1_xboole_0 = sK1 ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_254,c_19,c_17]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_876,plain,
% 1.26/0.98      ( r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
% 1.26/0.98      | ~ r2_hidden(sK2,sK0)
% 1.26/0.98      | k1_xboole_0 = sK1 ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_258]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_877,plain,
% 1.26/0.98      ( k1_xboole_0 = sK1
% 1.26/0.98      | r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) = iProver_top
% 1.26/0.98      | r2_hidden(sK2,sK0) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_7,plain,
% 1.26/0.98      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_785,plain,
% 1.26/0.98      ( r2_hidden(X0,sK0) | ~ m1_subset_1(X0,sK0) | v1_xboole_0(sK0) ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_832,plain,
% 1.26/0.98      ( r2_hidden(sK2,sK0) | ~ m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_785]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_833,plain,
% 1.26/0.98      ( r2_hidden(sK2,sK0) = iProver_top
% 1.26/0.98      | m1_subset_1(sK2,sK0) != iProver_top
% 1.26/0.98      | v1_xboole_0(sK0) = iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_395,plain,
% 1.26/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.26/0.98      theory(equality) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_765,plain,
% 1.26/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_395]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_767,plain,
% 1.26/0.98      ( v1_xboole_0(sK1)
% 1.26/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 1.26/0.98      | sK1 != k1_xboole_0 ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_765]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_0,plain,
% 1.26/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_61,plain,
% 1.26/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1,plain,
% 1.26/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_58,plain,
% 1.26/0.98      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.26/0.98      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.26/0.98      | v1_xboole_0(k1_xboole_0) ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_5,plain,
% 1.26/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.26/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_53,plain,
% 1.26/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_8,plain,
% 1.26/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_46,plain,
% 1.26/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 1.26/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.26/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_25,plain,
% 1.26/0.98      ( m1_subset_1(sK2,sK0) = iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_21,negated_conjecture,
% 1.26/0.98      ( ~ v1_xboole_0(sK1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_23,plain,
% 1.26/0.98      ( v1_xboole_0(sK0) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(contradiction,plain,
% 1.26/0.98      ( $false ),
% 1.26/0.98      inference(minisat,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_953,c_954,c_884,c_877,c_833,c_767,c_61,c_58,c_53,c_46,
% 1.26/0.98                 c_25,c_21,c_23]) ).
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.26/0.98  
% 1.26/0.98  ------                               Statistics
% 1.26/0.98  
% 1.26/0.98  ------ General
% 1.26/0.98  
% 1.26/0.98  abstr_ref_over_cycles:                  0
% 1.26/0.98  abstr_ref_under_cycles:                 0
% 1.26/0.98  gc_basic_clause_elim:                   0
% 1.26/0.98  forced_gc_time:                         0
% 1.26/0.98  parsing_time:                           0.008
% 1.26/0.98  unif_index_cands_time:                  0.
% 1.26/0.98  unif_index_add_time:                    0.
% 1.26/0.98  orderings_time:                         0.
% 1.26/0.98  out_proof_time:                         0.009
% 1.26/0.98  total_time:                             0.062
% 1.26/0.98  num_of_symbols:                         48
% 1.26/0.98  num_of_terms:                           736
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing
% 1.26/0.98  
% 1.26/0.98  num_of_splits:                          0
% 1.26/0.98  num_of_split_atoms:                     0
% 1.26/0.98  num_of_reused_defs:                     0
% 1.26/0.98  num_eq_ax_congr_red:                    7
% 1.26/0.98  num_of_sem_filtered_clauses:            1
% 1.26/0.98  num_of_subtypes:                        0
% 1.26/0.98  monotx_restored_types:                  0
% 1.26/0.98  sat_num_of_epr_types:                   0
% 1.26/0.98  sat_num_of_non_cyclic_types:            0
% 1.26/0.98  sat_guarded_non_collapsed_types:        0
% 1.26/0.98  num_pure_diseq_elim:                    0
% 1.26/0.98  simp_replaced_by:                       0
% 1.26/0.98  res_preprocessed:                       90
% 1.26/0.98  prep_upred:                             0
% 1.26/0.98  prep_unflattend:                        13
% 1.26/0.98  smt_new_axioms:                         0
% 1.26/0.98  pred_elim_cands:                        3
% 1.26/0.98  pred_elim:                              4
% 1.26/0.98  pred_elim_cl:                           5
% 1.26/0.98  pred_elim_cycles:                       6
% 1.26/0.98  merged_defs:                            0
% 1.26/0.98  merged_defs_ncl:                        0
% 1.26/0.98  bin_hyper_res:                          0
% 1.26/0.98  prep_cycles:                            4
% 1.26/0.98  pred_elim_time:                         0.002
% 1.26/0.98  splitting_time:                         0.
% 1.26/0.98  sem_filter_time:                        0.
% 1.26/0.98  monotx_time:                            0.
% 1.26/0.98  subtype_inf_time:                       0.
% 1.26/0.98  
% 1.26/0.98  ------ Problem properties
% 1.26/0.98  
% 1.26/0.98  clauses:                                16
% 1.26/0.98  conjectures:                            5
% 1.26/0.98  epr:                                    5
% 1.26/0.98  horn:                                   13
% 1.26/0.98  ground:                                 6
% 1.26/0.98  unary:                                  9
% 1.26/0.98  binary:                                 2
% 1.26/0.98  lits:                                   28
% 1.26/0.98  lits_eq:                                7
% 1.26/0.98  fd_pure:                                0
% 1.26/0.98  fd_pseudo:                              0
% 1.26/0.98  fd_cond:                                1
% 1.26/0.98  fd_pseudo_cond:                         0
% 1.26/0.98  ac_symbols:                             0
% 1.26/0.98  
% 1.26/0.98  ------ Propositional Solver
% 1.26/0.98  
% 1.26/0.98  prop_solver_calls:                      24
% 1.26/0.98  prop_fast_solver_calls:                 429
% 1.26/0.98  smt_solver_calls:                       0
% 1.26/0.98  smt_fast_solver_calls:                  0
% 1.26/0.98  prop_num_of_clauses:                    241
% 1.26/0.98  prop_preprocess_simplified:             2199
% 1.26/0.98  prop_fo_subsumed:                       9
% 1.26/0.98  prop_solver_time:                       0.
% 1.26/0.98  smt_solver_time:                        0.
% 1.26/0.98  smt_fast_solver_time:                   0.
% 1.26/0.98  prop_fast_solver_time:                  0.
% 1.26/0.98  prop_unsat_core_time:                   0.
% 1.26/0.98  
% 1.26/0.98  ------ QBF
% 1.26/0.98  
% 1.26/0.98  qbf_q_res:                              0
% 1.26/0.98  qbf_num_tautologies:                    0
% 1.26/0.98  qbf_prep_cycles:                        0
% 1.26/0.98  
% 1.26/0.98  ------ BMC1
% 1.26/0.98  
% 1.26/0.98  bmc1_current_bound:                     -1
% 1.26/0.98  bmc1_last_solved_bound:                 -1
% 1.26/0.98  bmc1_unsat_core_size:                   -1
% 1.26/0.98  bmc1_unsat_core_parents_size:           -1
% 1.26/0.98  bmc1_merge_next_fun:                    0
% 1.26/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.26/0.98  
% 1.26/0.98  ------ Instantiation
% 1.26/0.98  
% 1.26/0.98  inst_num_of_clauses:                    81
% 1.26/0.98  inst_num_in_passive:                    4
% 1.26/0.98  inst_num_in_active:                     52
% 1.26/0.98  inst_num_in_unprocessed:                24
% 1.26/0.98  inst_num_of_loops:                      55
% 1.26/0.98  inst_num_of_learning_restarts:          0
% 1.26/0.98  inst_num_moves_active_passive:          1
% 1.26/0.98  inst_lit_activity:                      0
% 1.26/0.98  inst_lit_activity_moves:                0
% 1.26/0.98  inst_num_tautologies:                   0
% 1.26/0.98  inst_num_prop_implied:                  0
% 1.26/0.98  inst_num_existing_simplified:           0
% 1.26/0.98  inst_num_eq_res_simplified:             0
% 1.26/0.98  inst_num_child_elim:                    0
% 1.26/0.98  inst_num_of_dismatching_blockings:      2
% 1.26/0.98  inst_num_of_non_proper_insts:           40
% 1.26/0.98  inst_num_of_duplicates:                 0
% 1.26/0.98  inst_inst_num_from_inst_to_res:         0
% 1.26/0.98  inst_dismatching_checking_time:         0.
% 1.26/0.98  
% 1.26/0.98  ------ Resolution
% 1.26/0.98  
% 1.26/0.98  res_num_of_clauses:                     0
% 1.26/0.98  res_num_in_passive:                     0
% 1.26/0.98  res_num_in_active:                      0
% 1.26/0.98  res_num_of_loops:                       94
% 1.26/0.98  res_forward_subset_subsumed:            6
% 1.26/0.98  res_backward_subset_subsumed:           0
% 1.26/0.98  res_forward_subsumed:                   0
% 1.26/0.98  res_backward_subsumed:                  0
% 1.26/0.98  res_forward_subsumption_resolution:     0
% 1.26/0.98  res_backward_subsumption_resolution:    0
% 1.26/0.98  res_clause_to_clause_subsumption:       19
% 1.26/0.98  res_orphan_elimination:                 0
% 1.26/0.98  res_tautology_del:                      2
% 1.26/0.98  res_num_eq_res_simplified:              0
% 1.26/0.98  res_num_sel_changes:                    0
% 1.26/0.98  res_moves_from_active_to_pass:          0
% 1.26/0.98  
% 1.26/0.98  ------ Superposition
% 1.26/0.98  
% 1.26/0.98  sup_time_total:                         0.
% 1.26/0.98  sup_time_generating:                    0.
% 1.26/0.98  sup_time_sim_full:                      0.
% 1.26/0.98  sup_time_sim_immed:                     0.
% 1.26/0.98  
% 1.26/0.98  sup_num_of_clauses:                     17
% 1.26/0.98  sup_num_in_active:                      9
% 1.26/0.98  sup_num_in_passive:                     8
% 1.26/0.98  sup_num_of_loops:                       10
% 1.26/0.98  sup_fw_superposition:                   1
% 1.26/0.98  sup_bw_superposition:                   0
% 1.26/0.98  sup_immediate_simplified:               0
% 1.26/0.98  sup_given_eliminated:                   0
% 1.26/0.98  comparisons_done:                       0
% 1.26/0.98  comparisons_avoided:                    0
% 1.26/0.98  
% 1.26/0.98  ------ Simplifications
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  sim_fw_subset_subsumed:                 0
% 1.26/0.98  sim_bw_subset_subsumed:                 0
% 1.26/0.98  sim_fw_subsumed:                        0
% 1.26/0.98  sim_bw_subsumed:                        0
% 1.26/0.98  sim_fw_subsumption_res:                 0
% 1.26/0.98  sim_bw_subsumption_res:                 0
% 1.26/0.98  sim_tautology_del:                      0
% 1.26/0.98  sim_eq_tautology_del:                   0
% 1.26/0.98  sim_eq_res_simp:                        0
% 1.26/0.98  sim_fw_demodulated:                     0
% 1.26/0.98  sim_bw_demodulated:                     1
% 1.26/0.98  sim_light_normalised:                   0
% 1.26/0.98  sim_joinable_taut:                      0
% 1.26/0.98  sim_joinable_simp:                      0
% 1.26/0.98  sim_ac_normalised:                      0
% 1.26/0.98  sim_smt_subsumption:                    0
% 1.26/0.98  
%------------------------------------------------------------------------------
