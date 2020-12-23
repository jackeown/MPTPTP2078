%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:20 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 182 expanded)
%              Number of clauses        :   46 (  70 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   18
%              Number of atoms          :  255 ( 641 expanded)
%              Number of equality atoms :   73 (  77 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK1(X0,X1,X2),X2)
            & r2_hidden(sK1(X0,X1,X2),X1)
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f18])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(X1,sK4)
        & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,sK4))
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK3,X2)
          & r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(sK3,sK4)
    & r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f23,f22])).

fof(f39,plain,(
    r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X1,X0,X2),X0)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_123,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_122])).

cnf(c_155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_123])).

cnf(c_622,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_156,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X2,X0),X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_123])).

cnf(c_621,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1(X1,X2,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_629,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1878,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(X2,X0) = iProver_top
    | r1_tarski(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(sK1(k1_zfmisc_1(X1),X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_629])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_627,plain,
    ( r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_625,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_123])).

cnf(c_620,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_153,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_123])).

cnf(c_624,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_153])).

cnf(c_1600,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k3_subset_1(X1,X2),X3) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k7_setfam_1(X1,X0),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_624])).

cnf(c_1737,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k3_subset_1(sK2,X0),X1) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k7_setfam_1(sK2,sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_1600])).

cnf(c_2275,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k3_subset_1(sK2,X0),k7_setfam_1(sK2,sK4)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_1737])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_123])).

cnf(c_619,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_2284,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_619])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2369,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2284,c_17])).

cnf(c_2659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(sK2),X1,X0),sK4) = iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(sK2),X1,X0),sK3) != iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(X1,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_2369])).

cnf(c_3205,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(sK2),sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK3,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_2659])).

cnf(c_16,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_761,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | r1_tarski(sK3,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_762,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r1_tarski(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_3718,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(sK2),sK3,X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3205,c_16,c_762])).

cnf(c_3719,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(sK2),sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3718])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0,X2),X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_154,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X2,X0),X0)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_123])).

cnf(c_623,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X2,X0),X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_3728,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r1_tarski(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3719,c_623])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3728,c_762,c_19,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:07:06 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 2.27/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.01  
% 2.27/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/1.01  
% 2.27/1.01  ------  iProver source info
% 2.27/1.01  
% 2.27/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.27/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/1.01  git: non_committed_changes: false
% 2.27/1.01  git: last_make_outside_of_git: false
% 2.27/1.01  
% 2.27/1.01  ------ 
% 2.27/1.01  
% 2.27/1.01  ------ Input Options
% 2.27/1.01  
% 2.27/1.01  --out_options                           all
% 2.27/1.01  --tptp_safe_out                         true
% 2.27/1.01  --problem_path                          ""
% 2.27/1.01  --include_path                          ""
% 2.27/1.01  --clausifier                            res/vclausify_rel
% 2.27/1.01  --clausifier_options                    --mode clausify
% 2.27/1.01  --stdin                                 false
% 2.27/1.01  --stats_out                             all
% 2.27/1.01  
% 2.27/1.01  ------ General Options
% 2.27/1.01  
% 2.27/1.01  --fof                                   false
% 2.27/1.01  --time_out_real                         305.
% 2.27/1.01  --time_out_virtual                      -1.
% 2.27/1.01  --symbol_type_check                     false
% 2.27/1.01  --clausify_out                          false
% 2.27/1.01  --sig_cnt_out                           false
% 2.27/1.01  --trig_cnt_out                          false
% 2.27/1.01  --trig_cnt_out_tolerance                1.
% 2.27/1.01  --trig_cnt_out_sk_spl                   false
% 2.27/1.01  --abstr_cl_out                          false
% 2.27/1.01  
% 2.27/1.01  ------ Global Options
% 2.27/1.01  
% 2.27/1.01  --schedule                              default
% 2.27/1.01  --add_important_lit                     false
% 2.27/1.01  --prop_solver_per_cl                    1000
% 2.27/1.01  --min_unsat_core                        false
% 2.27/1.01  --soft_assumptions                      false
% 2.27/1.01  --soft_lemma_size                       3
% 2.27/1.01  --prop_impl_unit_size                   0
% 2.27/1.01  --prop_impl_unit                        []
% 2.27/1.01  --share_sel_clauses                     true
% 2.27/1.01  --reset_solvers                         false
% 2.27/1.01  --bc_imp_inh                            [conj_cone]
% 2.27/1.01  --conj_cone_tolerance                   3.
% 2.27/1.01  --extra_neg_conj                        none
% 2.27/1.01  --large_theory_mode                     true
% 2.27/1.01  --prolific_symb_bound                   200
% 2.27/1.01  --lt_threshold                          2000
% 2.27/1.01  --clause_weak_htbl                      true
% 2.27/1.01  --gc_record_bc_elim                     false
% 2.27/1.01  
% 2.27/1.01  ------ Preprocessing Options
% 2.27/1.01  
% 2.27/1.01  --preprocessing_flag                    true
% 2.27/1.01  --time_out_prep_mult                    0.1
% 2.27/1.01  --splitting_mode                        input
% 2.27/1.01  --splitting_grd                         true
% 2.27/1.01  --splitting_cvd                         false
% 2.27/1.01  --splitting_cvd_svl                     false
% 2.27/1.01  --splitting_nvd                         32
% 2.27/1.01  --sub_typing                            true
% 2.27/1.01  --prep_gs_sim                           true
% 2.27/1.01  --prep_unflatten                        true
% 2.27/1.01  --prep_res_sim                          true
% 2.27/1.01  --prep_upred                            true
% 2.27/1.01  --prep_sem_filter                       exhaustive
% 2.27/1.01  --prep_sem_filter_out                   false
% 2.27/1.01  --pred_elim                             true
% 2.27/1.01  --res_sim_input                         true
% 2.27/1.01  --eq_ax_congr_red                       true
% 2.27/1.01  --pure_diseq_elim                       true
% 2.27/1.01  --brand_transform                       false
% 2.27/1.01  --non_eq_to_eq                          false
% 2.27/1.01  --prep_def_merge                        true
% 2.27/1.01  --prep_def_merge_prop_impl              false
% 2.27/1.01  --prep_def_merge_mbd                    true
% 2.27/1.01  --prep_def_merge_tr_red                 false
% 2.27/1.01  --prep_def_merge_tr_cl                  false
% 2.27/1.01  --smt_preprocessing                     true
% 2.27/1.01  --smt_ac_axioms                         fast
% 2.27/1.01  --preprocessed_out                      false
% 2.27/1.01  --preprocessed_stats                    false
% 2.27/1.01  
% 2.27/1.01  ------ Abstraction refinement Options
% 2.27/1.01  
% 2.27/1.01  --abstr_ref                             []
% 2.27/1.01  --abstr_ref_prep                        false
% 2.27/1.01  --abstr_ref_until_sat                   false
% 2.27/1.01  --abstr_ref_sig_restrict                funpre
% 2.27/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.01  --abstr_ref_under                       []
% 2.27/1.01  
% 2.27/1.01  ------ SAT Options
% 2.27/1.01  
% 2.27/1.01  --sat_mode                              false
% 2.27/1.01  --sat_fm_restart_options                ""
% 2.27/1.01  --sat_gr_def                            false
% 2.27/1.01  --sat_epr_types                         true
% 2.27/1.01  --sat_non_cyclic_types                  false
% 2.27/1.01  --sat_finite_models                     false
% 2.27/1.01  --sat_fm_lemmas                         false
% 2.27/1.01  --sat_fm_prep                           false
% 2.27/1.01  --sat_fm_uc_incr                        true
% 2.27/1.01  --sat_out_model                         small
% 2.27/1.01  --sat_out_clauses                       false
% 2.27/1.01  
% 2.27/1.01  ------ QBF Options
% 2.27/1.01  
% 2.27/1.01  --qbf_mode                              false
% 2.27/1.01  --qbf_elim_univ                         false
% 2.27/1.01  --qbf_dom_inst                          none
% 2.27/1.01  --qbf_dom_pre_inst                      false
% 2.27/1.01  --qbf_sk_in                             false
% 2.27/1.01  --qbf_pred_elim                         true
% 2.27/1.01  --qbf_split                             512
% 2.27/1.01  
% 2.27/1.01  ------ BMC1 Options
% 2.27/1.01  
% 2.27/1.01  --bmc1_incremental                      false
% 2.27/1.01  --bmc1_axioms                           reachable_all
% 2.27/1.01  --bmc1_min_bound                        0
% 2.27/1.01  --bmc1_max_bound                        -1
% 2.27/1.01  --bmc1_max_bound_default                -1
% 2.27/1.01  --bmc1_symbol_reachability              true
% 2.27/1.01  --bmc1_property_lemmas                  false
% 2.27/1.01  --bmc1_k_induction                      false
% 2.27/1.01  --bmc1_non_equiv_states                 false
% 2.27/1.01  --bmc1_deadlock                         false
% 2.27/1.01  --bmc1_ucm                              false
% 2.27/1.01  --bmc1_add_unsat_core                   none
% 2.27/1.01  --bmc1_unsat_core_children              false
% 2.27/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.01  --bmc1_out_stat                         full
% 2.27/1.01  --bmc1_ground_init                      false
% 2.27/1.01  --bmc1_pre_inst_next_state              false
% 2.27/1.01  --bmc1_pre_inst_state                   false
% 2.27/1.01  --bmc1_pre_inst_reach_state             false
% 2.27/1.01  --bmc1_out_unsat_core                   false
% 2.27/1.01  --bmc1_aig_witness_out                  false
% 2.27/1.01  --bmc1_verbose                          false
% 2.27/1.01  --bmc1_dump_clauses_tptp                false
% 2.27/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.01  --bmc1_dump_file                        -
% 2.27/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.01  --bmc1_ucm_extend_mode                  1
% 2.27/1.01  --bmc1_ucm_init_mode                    2
% 2.27/1.01  --bmc1_ucm_cone_mode                    none
% 2.27/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.01  --bmc1_ucm_relax_model                  4
% 2.27/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.01  --bmc1_ucm_layered_model                none
% 2.27/1.01  --bmc1_ucm_max_lemma_size               10
% 2.27/1.01  
% 2.27/1.01  ------ AIG Options
% 2.27/1.01  
% 2.27/1.01  --aig_mode                              false
% 2.27/1.01  
% 2.27/1.01  ------ Instantiation Options
% 2.27/1.01  
% 2.27/1.01  --instantiation_flag                    true
% 2.27/1.01  --inst_sos_flag                         false
% 2.27/1.01  --inst_sos_phase                        true
% 2.27/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.01  --inst_lit_sel_side                     num_symb
% 2.27/1.01  --inst_solver_per_active                1400
% 2.27/1.01  --inst_solver_calls_frac                1.
% 2.27/1.01  --inst_passive_queue_type               priority_queues
% 2.27/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.01  --inst_passive_queues_freq              [25;2]
% 2.27/1.01  --inst_dismatching                      true
% 2.27/1.01  --inst_eager_unprocessed_to_passive     true
% 2.27/1.01  --inst_prop_sim_given                   true
% 2.27/1.01  --inst_prop_sim_new                     false
% 2.27/1.01  --inst_subs_new                         false
% 2.27/1.01  --inst_eq_res_simp                      false
% 2.27/1.01  --inst_subs_given                       false
% 2.27/1.01  --inst_orphan_elimination               true
% 2.27/1.01  --inst_learning_loop_flag               true
% 2.27/1.01  --inst_learning_start                   3000
% 2.27/1.01  --inst_learning_factor                  2
% 2.27/1.01  --inst_start_prop_sim_after_learn       3
% 2.27/1.01  --inst_sel_renew                        solver
% 2.27/1.01  --inst_lit_activity_flag                true
% 2.27/1.01  --inst_restr_to_given                   false
% 2.27/1.01  --inst_activity_threshold               500
% 2.27/1.01  --inst_out_proof                        true
% 2.27/1.01  
% 2.27/1.01  ------ Resolution Options
% 2.27/1.01  
% 2.27/1.01  --resolution_flag                       true
% 2.27/1.01  --res_lit_sel                           adaptive
% 2.27/1.01  --res_lit_sel_side                      none
% 2.27/1.01  --res_ordering                          kbo
% 2.27/1.01  --res_to_prop_solver                    active
% 2.27/1.01  --res_prop_simpl_new                    false
% 2.27/1.01  --res_prop_simpl_given                  true
% 2.27/1.01  --res_passive_queue_type                priority_queues
% 2.27/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.01  --res_passive_queues_freq               [15;5]
% 2.27/1.01  --res_forward_subs                      full
% 2.27/1.01  --res_backward_subs                     full
% 2.27/1.01  --res_forward_subs_resolution           true
% 2.27/1.01  --res_backward_subs_resolution          true
% 2.27/1.01  --res_orphan_elimination                true
% 2.27/1.01  --res_time_limit                        2.
% 2.27/1.01  --res_out_proof                         true
% 2.27/1.01  
% 2.27/1.01  ------ Superposition Options
% 2.27/1.01  
% 2.27/1.01  --superposition_flag                    true
% 2.27/1.01  --sup_passive_queue_type                priority_queues
% 2.27/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.01  --demod_completeness_check              fast
% 2.27/1.01  --demod_use_ground                      true
% 2.27/1.01  --sup_to_prop_solver                    passive
% 2.27/1.01  --sup_prop_simpl_new                    true
% 2.27/1.01  --sup_prop_simpl_given                  true
% 2.27/1.01  --sup_fun_splitting                     false
% 2.27/1.01  --sup_smt_interval                      50000
% 2.27/1.01  
% 2.27/1.01  ------ Superposition Simplification Setup
% 2.27/1.01  
% 2.27/1.01  --sup_indices_passive                   []
% 2.27/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.01  --sup_full_bw                           [BwDemod]
% 2.27/1.01  --sup_immed_triv                        [TrivRules]
% 2.27/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.01  --sup_immed_bw_main                     []
% 2.27/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.01  
% 2.27/1.01  ------ Combination Options
% 2.27/1.01  
% 2.27/1.01  --comb_res_mult                         3
% 2.27/1.01  --comb_sup_mult                         2
% 2.27/1.01  --comb_inst_mult                        10
% 2.27/1.01  
% 2.27/1.01  ------ Debug Options
% 2.27/1.01  
% 2.27/1.01  --dbg_backtrace                         false
% 2.27/1.01  --dbg_dump_prop_clauses                 false
% 2.27/1.01  --dbg_dump_prop_clauses_file            -
% 2.27/1.01  --dbg_out_stat                          false
% 2.27/1.01  ------ Parsing...
% 2.27/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/1.01  
% 2.27/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.27/1.01  
% 2.27/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/1.01  
% 2.27/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/1.01  ------ Proving...
% 2.27/1.01  ------ Problem Properties 
% 2.27/1.01  
% 2.27/1.01  
% 2.27/1.01  clauses                                 16
% 2.27/1.01  conjectures                             4
% 2.27/1.01  EPR                                     2
% 2.27/1.01  Horn                                    13
% 2.27/1.01  unary                                   4
% 2.27/1.01  binary                                  4
% 2.27/1.01  lits                                    41
% 2.27/1.01  lits eq                                 2
% 2.27/1.01  fd_pure                                 0
% 2.27/1.01  fd_pseudo                               0
% 2.27/1.01  fd_cond                                 0
% 2.27/1.01  fd_pseudo_cond                          2
% 2.27/1.01  AC symbols                              0
% 2.27/1.01  
% 2.27/1.01  ------ Schedule dynamic 5 is on 
% 2.27/1.01  
% 2.27/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/1.01  
% 2.27/1.01  
% 2.27/1.01  ------ 
% 2.27/1.01  Current options:
% 2.27/1.01  ------ 
% 2.27/1.01  
% 2.27/1.01  ------ Input Options
% 2.27/1.01  
% 2.27/1.01  --out_options                           all
% 2.27/1.01  --tptp_safe_out                         true
% 2.27/1.01  --problem_path                          ""
% 2.27/1.01  --include_path                          ""
% 2.27/1.01  --clausifier                            res/vclausify_rel
% 2.27/1.01  --clausifier_options                    --mode clausify
% 2.27/1.01  --stdin                                 false
% 2.27/1.01  --stats_out                             all
% 2.27/1.01  
% 2.27/1.01  ------ General Options
% 2.27/1.01  
% 2.27/1.01  --fof                                   false
% 2.27/1.01  --time_out_real                         305.
% 2.27/1.01  --time_out_virtual                      -1.
% 2.27/1.01  --symbol_type_check                     false
% 2.27/1.01  --clausify_out                          false
% 2.27/1.01  --sig_cnt_out                           false
% 2.27/1.01  --trig_cnt_out                          false
% 2.27/1.01  --trig_cnt_out_tolerance                1.
% 2.27/1.01  --trig_cnt_out_sk_spl                   false
% 2.27/1.01  --abstr_cl_out                          false
% 2.27/1.01  
% 2.27/1.01  ------ Global Options
% 2.27/1.01  
% 2.27/1.01  --schedule                              default
% 2.27/1.01  --add_important_lit                     false
% 2.27/1.01  --prop_solver_per_cl                    1000
% 2.27/1.01  --min_unsat_core                        false
% 2.27/1.01  --soft_assumptions                      false
% 2.27/1.01  --soft_lemma_size                       3
% 2.27/1.01  --prop_impl_unit_size                   0
% 2.27/1.01  --prop_impl_unit                        []
% 2.27/1.01  --share_sel_clauses                     true
% 2.27/1.01  --reset_solvers                         false
% 2.27/1.01  --bc_imp_inh                            [conj_cone]
% 2.27/1.01  --conj_cone_tolerance                   3.
% 2.27/1.01  --extra_neg_conj                        none
% 2.27/1.01  --large_theory_mode                     true
% 2.27/1.01  --prolific_symb_bound                   200
% 2.27/1.01  --lt_threshold                          2000
% 2.27/1.01  --clause_weak_htbl                      true
% 2.27/1.01  --gc_record_bc_elim                     false
% 2.27/1.01  
% 2.27/1.01  ------ Preprocessing Options
% 2.27/1.01  
% 2.27/1.01  --preprocessing_flag                    true
% 2.27/1.01  --time_out_prep_mult                    0.1
% 2.27/1.01  --splitting_mode                        input
% 2.27/1.01  --splitting_grd                         true
% 2.27/1.01  --splitting_cvd                         false
% 2.27/1.01  --splitting_cvd_svl                     false
% 2.27/1.01  --splitting_nvd                         32
% 2.27/1.01  --sub_typing                            true
% 2.27/1.01  --prep_gs_sim                           true
% 2.27/1.01  --prep_unflatten                        true
% 2.27/1.01  --prep_res_sim                          true
% 2.27/1.01  --prep_upred                            true
% 2.27/1.01  --prep_sem_filter                       exhaustive
% 2.27/1.01  --prep_sem_filter_out                   false
% 2.27/1.01  --pred_elim                             true
% 2.27/1.01  --res_sim_input                         true
% 2.27/1.01  --eq_ax_congr_red                       true
% 2.27/1.01  --pure_diseq_elim                       true
% 2.27/1.01  --brand_transform                       false
% 2.27/1.01  --non_eq_to_eq                          false
% 2.27/1.01  --prep_def_merge                        true
% 2.27/1.01  --prep_def_merge_prop_impl              false
% 2.27/1.01  --prep_def_merge_mbd                    true
% 2.27/1.01  --prep_def_merge_tr_red                 false
% 2.27/1.01  --prep_def_merge_tr_cl                  false
% 2.27/1.01  --smt_preprocessing                     true
% 2.27/1.01  --smt_ac_axioms                         fast
% 2.27/1.01  --preprocessed_out                      false
% 2.27/1.01  --preprocessed_stats                    false
% 2.27/1.01  
% 2.27/1.01  ------ Abstraction refinement Options
% 2.27/1.01  
% 2.27/1.01  --abstr_ref                             []
% 2.27/1.01  --abstr_ref_prep                        false
% 2.27/1.01  --abstr_ref_until_sat                   false
% 2.27/1.01  --abstr_ref_sig_restrict                funpre
% 2.27/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.01  --abstr_ref_under                       []
% 2.27/1.01  
% 2.27/1.01  ------ SAT Options
% 2.27/1.01  
% 2.27/1.01  --sat_mode                              false
% 2.27/1.01  --sat_fm_restart_options                ""
% 2.27/1.01  --sat_gr_def                            false
% 2.27/1.01  --sat_epr_types                         true
% 2.27/1.01  --sat_non_cyclic_types                  false
% 2.27/1.01  --sat_finite_models                     false
% 2.27/1.01  --sat_fm_lemmas                         false
% 2.27/1.01  --sat_fm_prep                           false
% 2.27/1.01  --sat_fm_uc_incr                        true
% 2.27/1.01  --sat_out_model                         small
% 2.27/1.01  --sat_out_clauses                       false
% 2.27/1.01  
% 2.27/1.01  ------ QBF Options
% 2.27/1.01  
% 2.27/1.01  --qbf_mode                              false
% 2.27/1.01  --qbf_elim_univ                         false
% 2.27/1.01  --qbf_dom_inst                          none
% 2.27/1.01  --qbf_dom_pre_inst                      false
% 2.27/1.01  --qbf_sk_in                             false
% 2.27/1.01  --qbf_pred_elim                         true
% 2.27/1.01  --qbf_split                             512
% 2.27/1.01  
% 2.27/1.01  ------ BMC1 Options
% 2.27/1.01  
% 2.27/1.01  --bmc1_incremental                      false
% 2.27/1.01  --bmc1_axioms                           reachable_all
% 2.27/1.01  --bmc1_min_bound                        0
% 2.27/1.01  --bmc1_max_bound                        -1
% 2.27/1.01  --bmc1_max_bound_default                -1
% 2.27/1.01  --bmc1_symbol_reachability              true
% 2.27/1.01  --bmc1_property_lemmas                  false
% 2.27/1.01  --bmc1_k_induction                      false
% 2.27/1.01  --bmc1_non_equiv_states                 false
% 2.27/1.01  --bmc1_deadlock                         false
% 2.27/1.01  --bmc1_ucm                              false
% 2.27/1.01  --bmc1_add_unsat_core                   none
% 2.27/1.01  --bmc1_unsat_core_children              false
% 2.27/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.01  --bmc1_out_stat                         full
% 2.27/1.01  --bmc1_ground_init                      false
% 2.27/1.01  --bmc1_pre_inst_next_state              false
% 2.27/1.01  --bmc1_pre_inst_state                   false
% 2.27/1.01  --bmc1_pre_inst_reach_state             false
% 2.27/1.01  --bmc1_out_unsat_core                   false
% 2.27/1.01  --bmc1_aig_witness_out                  false
% 2.27/1.01  --bmc1_verbose                          false
% 2.27/1.01  --bmc1_dump_clauses_tptp                false
% 2.27/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.01  --bmc1_dump_file                        -
% 2.27/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.01  --bmc1_ucm_extend_mode                  1
% 2.27/1.01  --bmc1_ucm_init_mode                    2
% 2.27/1.01  --bmc1_ucm_cone_mode                    none
% 2.27/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.01  --bmc1_ucm_relax_model                  4
% 2.27/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.01  --bmc1_ucm_layered_model                none
% 2.27/1.01  --bmc1_ucm_max_lemma_size               10
% 2.27/1.01  
% 2.27/1.01  ------ AIG Options
% 2.27/1.01  
% 2.27/1.01  --aig_mode                              false
% 2.27/1.01  
% 2.27/1.01  ------ Instantiation Options
% 2.27/1.01  
% 2.27/1.01  --instantiation_flag                    true
% 2.27/1.01  --inst_sos_flag                         false
% 2.27/1.01  --inst_sos_phase                        true
% 2.27/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.01  --inst_lit_sel_side                     none
% 2.27/1.01  --inst_solver_per_active                1400
% 2.27/1.01  --inst_solver_calls_frac                1.
% 2.27/1.01  --inst_passive_queue_type               priority_queues
% 2.27/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.01  --inst_passive_queues_freq              [25;2]
% 2.27/1.01  --inst_dismatching                      true
% 2.27/1.01  --inst_eager_unprocessed_to_passive     true
% 2.27/1.01  --inst_prop_sim_given                   true
% 2.27/1.01  --inst_prop_sim_new                     false
% 2.27/1.01  --inst_subs_new                         false
% 2.27/1.01  --inst_eq_res_simp                      false
% 2.27/1.01  --inst_subs_given                       false
% 2.27/1.01  --inst_orphan_elimination               true
% 2.27/1.01  --inst_learning_loop_flag               true
% 2.27/1.01  --inst_learning_start                   3000
% 2.27/1.01  --inst_learning_factor                  2
% 2.27/1.01  --inst_start_prop_sim_after_learn       3
% 2.27/1.01  --inst_sel_renew                        solver
% 2.27/1.01  --inst_lit_activity_flag                true
% 2.27/1.01  --inst_restr_to_given                   false
% 2.27/1.01  --inst_activity_threshold               500
% 2.27/1.01  --inst_out_proof                        true
% 2.27/1.01  
% 2.27/1.01  ------ Resolution Options
% 2.27/1.01  
% 2.27/1.01  --resolution_flag                       false
% 2.27/1.01  --res_lit_sel                           adaptive
% 2.27/1.01  --res_lit_sel_side                      none
% 2.27/1.01  --res_ordering                          kbo
% 2.27/1.01  --res_to_prop_solver                    active
% 2.27/1.01  --res_prop_simpl_new                    false
% 2.27/1.01  --res_prop_simpl_given                  true
% 2.27/1.01  --res_passive_queue_type                priority_queues
% 2.27/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.01  --res_passive_queues_freq               [15;5]
% 2.27/1.01  --res_forward_subs                      full
% 2.27/1.01  --res_backward_subs                     full
% 2.27/1.01  --res_forward_subs_resolution           true
% 2.27/1.01  --res_backward_subs_resolution          true
% 2.27/1.01  --res_orphan_elimination                true
% 2.27/1.01  --res_time_limit                        2.
% 2.27/1.01  --res_out_proof                         true
% 2.27/1.01  
% 2.27/1.01  ------ Superposition Options
% 2.27/1.01  
% 2.27/1.01  --superposition_flag                    true
% 2.27/1.01  --sup_passive_queue_type                priority_queues
% 2.27/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.01  --demod_completeness_check              fast
% 2.27/1.01  --demod_use_ground                      true
% 2.27/1.01  --sup_to_prop_solver                    passive
% 2.27/1.01  --sup_prop_simpl_new                    true
% 2.27/1.01  --sup_prop_simpl_given                  true
% 2.27/1.01  --sup_fun_splitting                     false
% 2.27/1.01  --sup_smt_interval                      50000
% 2.27/1.01  
% 2.27/1.01  ------ Superposition Simplification Setup
% 2.27/1.01  
% 2.27/1.01  --sup_indices_passive                   []
% 2.27/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.01  --sup_full_bw                           [BwDemod]
% 2.27/1.01  --sup_immed_triv                        [TrivRules]
% 2.27/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.01  --sup_immed_bw_main                     []
% 2.27/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.01  
% 2.27/1.01  ------ Combination Options
% 2.27/1.01  
% 2.27/1.01  --comb_res_mult                         3
% 2.27/1.01  --comb_sup_mult                         2
% 2.27/1.01  --comb_inst_mult                        10
% 2.27/1.01  
% 2.27/1.01  ------ Debug Options
% 2.27/1.01  
% 2.27/1.01  --dbg_backtrace                         false
% 2.27/1.01  --dbg_dump_prop_clauses                 false
% 2.27/1.01  --dbg_dump_prop_clauses_file            -
% 2.27/1.01  --dbg_out_stat                          false
% 2.27/1.01  
% 2.27/1.01  
% 2.27/1.01  
% 2.27/1.01  
% 2.27/1.01  ------ Proving...
% 2.27/1.01  
% 2.27/1.01  
% 2.27/1.01  % SZS status Theorem for theBenchmark.p
% 2.27/1.01  
% 2.27/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/1.01  
% 2.27/1.01  fof(f3,axiom,(
% 2.27/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.27/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.01  
% 2.27/1.01  fof(f9,plain,(
% 2.27/1.01    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/1.01    inference(ennf_transformation,[],[f3])).
% 2.27/1.01  
% 2.27/1.01  fof(f10,plain,(
% 2.27/1.01    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/1.01    inference(flattening,[],[f9])).
% 2.27/1.01  
% 2.27/1.01  fof(f18,plain,(
% 2.27/1.01    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),X0)))),
% 2.27/1.01    introduced(choice_axiom,[])).
% 2.27/1.01  
% 2.27/1.01  fof(f19,plain,(
% 2.27/1.01    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f18])).
% 2.27/1.01  
% 2.27/1.01  fof(f31,plain,(
% 2.27/1.01    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/1.01    inference(cnf_transformation,[],[f19])).
% 2.27/1.01  
% 2.27/1.01  fof(f4,axiom,(
% 2.27/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.27/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.01  
% 2.27/1.01  fof(f20,plain,(
% 2.27/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.27/1.01    inference(nnf_transformation,[],[f4])).
% 2.27/1.01  
% 2.27/1.01  fof(f34,plain,(
% 2.27/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.27/1.01    inference(cnf_transformation,[],[f20])).
% 2.27/1.01  
% 2.27/1.01  fof(f30,plain,(
% 2.27/1.01    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/1.01    inference(cnf_transformation,[],[f19])).
% 2.27/1.01  
% 2.27/1.01  fof(f33,plain,(
% 2.27/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.27/1.01    inference(cnf_transformation,[],[f20])).
% 2.27/1.01  
% 2.27/1.01  fof(f6,conjecture,(
% 2.27/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 2.27/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.01  
% 2.27/1.01  fof(f7,negated_conjecture,(
% 2.27/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 2.27/1.01    inference(negated_conjecture,[],[f6])).
% 2.27/1.01  
% 2.27/1.01  fof(f12,plain,(
% 2.27/1.01    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.27/1.01    inference(ennf_transformation,[],[f7])).
% 2.27/1.01  
% 2.27/1.01  fof(f13,plain,(
% 2.27/1.01    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.27/1.01    inference(flattening,[],[f12])).
% 2.27/1.01  
% 2.27/1.01  fof(f23,plain,(
% 2.27/1.01    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(X1,sK4) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.27/1.01    introduced(choice_axiom,[])).
% 2.27/1.01  
% 2.27/1.01  fof(f22,plain,(
% 2.27/1.01    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(sK3,X2) & r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 2.27/1.01    introduced(choice_axiom,[])).
% 2.27/1.01  
% 2.27/1.01  fof(f24,plain,(
% 2.27/1.01    (~r1_tarski(sK3,sK4) & r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.27/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f23,f22])).
% 2.27/1.01  
% 2.27/1.01  fof(f39,plain,(
% 2.27/1.01    r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4))),
% 2.27/1.01    inference(cnf_transformation,[],[f24])).
% 2.27/1.01  
% 2.27/1.01  fof(f37,plain,(
% 2.27/1.01    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.27/1.01    inference(cnf_transformation,[],[f24])).
% 2.27/1.01  
% 2.27/1.01  fof(f5,axiom,(
% 2.27/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 2.27/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.01  
% 2.27/1.01  fof(f11,plain,(
% 2.27/1.01    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.27/1.01    inference(ennf_transformation,[],[f5])).
% 2.27/1.01  
% 2.27/1.01  fof(f21,plain,(
% 2.27/1.01    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.27/1.01    inference(nnf_transformation,[],[f11])).
% 2.27/1.01  
% 2.27/1.01  fof(f36,plain,(
% 2.27/1.01    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.27/1.01    inference(cnf_transformation,[],[f21])).
% 2.27/1.01  
% 2.27/1.01  fof(f2,axiom,(
% 2.27/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.27/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.01  
% 2.27/1.01  fof(f8,plain,(
% 2.27/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/1.01    inference(ennf_transformation,[],[f2])).
% 2.27/1.01  
% 2.27/1.01  fof(f29,plain,(
% 2.27/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/1.01    inference(cnf_transformation,[],[f8])).
% 2.27/1.01  
% 2.27/1.01  fof(f35,plain,(
% 2.27/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.27/1.01    inference(cnf_transformation,[],[f21])).
% 2.27/1.01  
% 2.27/1.01  fof(f38,plain,(
% 2.27/1.01    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.27/1.01    inference(cnf_transformation,[],[f24])).
% 2.27/1.01  
% 2.27/1.01  fof(f32,plain,(
% 2.27/1.01    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/1.01    inference(cnf_transformation,[],[f19])).
% 2.27/1.01  
% 2.27/1.01  fof(f40,plain,(
% 2.27/1.01    ~r1_tarski(sK3,sK4)),
% 2.27/1.01    inference(cnf_transformation,[],[f24])).
% 2.27/1.01  
% 2.27/1.01  cnf(c_6,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.27/1.01      | r2_hidden(sK1(X1,X0,X2),X0)
% 2.27/1.01      | r1_tarski(X0,X2) ),
% 2.27/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_8,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.27/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_122,plain,
% 2.27/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.27/1.01      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_123,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.27/1.01      inference(renaming,[status(thm)],[c_122]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_155,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.01      | r2_hidden(sK1(X1,X2,X0),X2)
% 2.27/1.01      | ~ r1_tarski(X2,X1)
% 2.27/1.01      | r1_tarski(X2,X0) ),
% 2.27/1.01      inference(bin_hyper_res,[status(thm)],[c_6,c_123]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_622,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.27/1.01      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 2.27/1.01      | r1_tarski(X2,X1) != iProver_top
% 2.27/1.01      | r1_tarski(X2,X0) = iProver_top ),
% 2.27/1.01      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_7,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.27/1.01      | m1_subset_1(sK1(X1,X0,X2),X1)
% 2.27/1.01      | r1_tarski(X0,X2) ),
% 2.27/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_156,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.01      | m1_subset_1(sK1(X1,X2,X0),X1)
% 2.27/1.01      | ~ r1_tarski(X2,X1)
% 2.27/1.01      | r1_tarski(X2,X0) ),
% 2.27/1.01      inference(bin_hyper_res,[status(thm)],[c_7,c_123]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_621,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.27/1.01      | m1_subset_1(sK1(X1,X2,X0),X1) = iProver_top
% 2.27/1.01      | r1_tarski(X2,X1) != iProver_top
% 2.27/1.01      | r1_tarski(X2,X0) = iProver_top ),
% 2.27/1.01      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_9,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.27/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_629,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.27/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.27/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_1878,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.27/1.01      | r1_tarski(X2,X0) = iProver_top
% 2.27/1.01      | r1_tarski(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.27/1.01      | r1_tarski(sK1(k1_zfmisc_1(X1),X2,X0),X1) = iProver_top ),
% 2.27/1.01      inference(superposition,[status(thm)],[c_621,c_629]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_13,negated_conjecture,
% 2.27/1.01      ( r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) ),
% 2.27/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_627,plain,
% 2.27/1.01      ( r1_tarski(k7_setfam_1(sK2,sK3),k7_setfam_1(sK2,sK4)) = iProver_top ),
% 2.27/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_15,negated_conjecture,
% 2.27/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.27/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_625,plain,
% 2.27/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.27/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_10,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.27/1.01      | ~ r2_hidden(X0,X2)
% 2.27/1.01      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 2.27/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_159,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.27/1.01      | ~ r2_hidden(X2,X0)
% 2.27/1.01      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
% 2.27/1.01      | ~ r1_tarski(X2,X1) ),
% 2.27/1.01      inference(bin_hyper_res,[status(thm)],[c_10,c_123]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_620,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.27/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.27/1.01      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) = iProver_top
% 2.27/1.01      | r1_tarski(X2,X1) != iProver_top ),
% 2.27/1.01      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_4,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.01      | ~ r2_hidden(X2,X0)
% 2.27/1.01      | r2_hidden(X2,X1) ),
% 2.27/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_153,plain,
% 2.27/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.27/1.01      inference(bin_hyper_res,[status(thm)],[c_4,c_123]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_624,plain,
% 2.27/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.27/1.01      | r2_hidden(X0,X2) = iProver_top
% 2.27/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 2.27/1.01      inference(predicate_to_equality,[status(thm)],[c_153]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_1600,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.27/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.27/1.01      | r2_hidden(k3_subset_1(X1,X2),X3) = iProver_top
% 2.27/1.01      | r1_tarski(X2,X1) != iProver_top
% 2.27/1.01      | r1_tarski(k7_setfam_1(X1,X0),X3) != iProver_top ),
% 2.27/1.01      inference(superposition,[status(thm)],[c_620,c_624]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_1737,plain,
% 2.27/1.01      ( r2_hidden(X0,sK3) != iProver_top
% 2.27/1.01      | r2_hidden(k3_subset_1(sK2,X0),X1) = iProver_top
% 2.27/1.01      | r1_tarski(X0,sK2) != iProver_top
% 2.27/1.01      | r1_tarski(k7_setfam_1(sK2,sK3),X1) != iProver_top ),
% 2.27/1.01      inference(superposition,[status(thm)],[c_625,c_1600]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_2275,plain,
% 2.27/1.01      ( r2_hidden(X0,sK3) != iProver_top
% 2.27/1.01      | r2_hidden(k3_subset_1(sK2,X0),k7_setfam_1(sK2,sK4)) = iProver_top
% 2.27/1.01      | r1_tarski(X0,sK2) != iProver_top ),
% 2.27/1.01      inference(superposition,[status(thm)],[c_627,c_1737]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_11,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.27/1.01      | r2_hidden(X0,X2)
% 2.27/1.01      | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 2.27/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_160,plain,
% 2.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.27/1.01      | r2_hidden(X2,X0)
% 2.27/1.01      | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
% 2.27/1.01      | ~ r1_tarski(X2,X1) ),
% 2.27/1.01      inference(bin_hyper_res,[status(thm)],[c_11,c_123]) ).
% 2.27/1.01  
% 2.27/1.01  cnf(c_619,plain,
% 2.27/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.27/1.02      | r2_hidden(X2,X0) = iProver_top
% 2.27/1.02      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) != iProver_top
% 2.27/1.02      | r1_tarski(X2,X1) != iProver_top ),
% 2.27/1.02      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_2284,plain,
% 2.27/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.27/1.02      | r2_hidden(X0,sK4) = iProver_top
% 2.27/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.27/1.02      | r1_tarski(X0,sK2) != iProver_top ),
% 2.27/1.02      inference(superposition,[status(thm)],[c_2275,c_619]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_14,negated_conjecture,
% 2.27/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.27/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_17,plain,
% 2.27/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.27/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_2369,plain,
% 2.27/1.02      ( r2_hidden(X0,sK4) = iProver_top
% 2.27/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.27/1.02      | r1_tarski(X0,sK2) != iProver_top ),
% 2.27/1.02      inference(global_propositional_subsumption,
% 2.27/1.02                [status(thm)],
% 2.27/1.02                [c_2284,c_17]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_2659,plain,
% 2.27/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.27/1.02      | r2_hidden(sK1(k1_zfmisc_1(sK2),X1,X0),sK4) = iProver_top
% 2.27/1.02      | r2_hidden(sK1(k1_zfmisc_1(sK2),X1,X0),sK3) != iProver_top
% 2.27/1.02      | r1_tarski(X1,X0) = iProver_top
% 2.27/1.02      | r1_tarski(X1,k1_zfmisc_1(sK2)) != iProver_top ),
% 2.27/1.02      inference(superposition,[status(thm)],[c_1878,c_2369]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_3205,plain,
% 2.27/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.27/1.02      | r2_hidden(sK1(k1_zfmisc_1(sK2),sK3,X0),sK4) = iProver_top
% 2.27/1.02      | r1_tarski(sK3,X0) = iProver_top
% 2.27/1.02      | r1_tarski(sK3,k1_zfmisc_1(sK2)) != iProver_top ),
% 2.27/1.02      inference(superposition,[status(thm)],[c_622,c_2659]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_16,plain,
% 2.27/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.27/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_761,plain,
% 2.27/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.27/1.02      | r1_tarski(sK3,k1_zfmisc_1(sK2)) ),
% 2.27/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_762,plain,
% 2.27/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.27/1.02      | r1_tarski(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.27/1.02      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_3718,plain,
% 2.27/1.02      ( r1_tarski(sK3,X0) = iProver_top
% 2.27/1.02      | r2_hidden(sK1(k1_zfmisc_1(sK2),sK3,X0),sK4) = iProver_top
% 2.27/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.27/1.02      inference(global_propositional_subsumption,
% 2.27/1.02                [status(thm)],
% 2.27/1.02                [c_3205,c_16,c_762]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_3719,plain,
% 2.27/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.27/1.02      | r2_hidden(sK1(k1_zfmisc_1(sK2),sK3,X0),sK4) = iProver_top
% 2.27/1.02      | r1_tarski(sK3,X0) = iProver_top ),
% 2.27/1.02      inference(renaming,[status(thm)],[c_3718]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_5,plain,
% 2.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.27/1.02      | ~ r2_hidden(sK1(X1,X0,X2),X2)
% 2.27/1.02      | r1_tarski(X0,X2) ),
% 2.27/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_154,plain,
% 2.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.02      | ~ r2_hidden(sK1(X1,X2,X0),X0)
% 2.27/1.02      | ~ r1_tarski(X2,X1)
% 2.27/1.02      | r1_tarski(X2,X0) ),
% 2.27/1.02      inference(bin_hyper_res,[status(thm)],[c_5,c_123]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_623,plain,
% 2.27/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.27/1.02      | r2_hidden(sK1(X1,X2,X0),X0) != iProver_top
% 2.27/1.02      | r1_tarski(X2,X1) != iProver_top
% 2.27/1.02      | r1_tarski(X2,X0) = iProver_top ),
% 2.27/1.02      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_3728,plain,
% 2.27/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.27/1.02      | r1_tarski(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 2.27/1.02      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.27/1.02      inference(superposition,[status(thm)],[c_3719,c_623]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_12,negated_conjecture,
% 2.27/1.02      ( ~ r1_tarski(sK3,sK4) ),
% 2.27/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(c_19,plain,
% 2.27/1.02      ( r1_tarski(sK3,sK4) != iProver_top ),
% 2.27/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.27/1.02  
% 2.27/1.02  cnf(contradiction,plain,
% 2.27/1.02      ( $false ),
% 2.27/1.02      inference(minisat,[status(thm)],[c_3728,c_762,c_19,c_17,c_16]) ).
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.02  
% 2.27/1.02  ------                               Statistics
% 2.27/1.02  
% 2.27/1.02  ------ General
% 2.27/1.02  
% 2.27/1.02  abstr_ref_over_cycles:                  0
% 2.27/1.02  abstr_ref_under_cycles:                 0
% 2.27/1.02  gc_basic_clause_elim:                   0
% 2.27/1.02  forced_gc_time:                         0
% 2.27/1.02  parsing_time:                           0.011
% 2.27/1.02  unif_index_cands_time:                  0.
% 2.27/1.02  unif_index_add_time:                    0.
% 2.27/1.02  orderings_time:                         0.
% 2.27/1.02  out_proof_time:                         0.008
% 2.27/1.02  total_time:                             0.18
% 2.27/1.02  num_of_symbols:                         42
% 2.27/1.02  num_of_terms:                           3264
% 2.27/1.02  
% 2.27/1.02  ------ Preprocessing
% 2.27/1.02  
% 2.27/1.02  num_of_splits:                          0
% 2.27/1.02  num_of_split_atoms:                     0
% 2.27/1.02  num_of_reused_defs:                     0
% 2.27/1.02  num_eq_ax_congr_red:                    14
% 2.27/1.02  num_of_sem_filtered_clauses:            1
% 2.27/1.02  num_of_subtypes:                        0
% 2.27/1.02  monotx_restored_types:                  0
% 2.27/1.02  sat_num_of_epr_types:                   0
% 2.27/1.02  sat_num_of_non_cyclic_types:            0
% 2.27/1.02  sat_guarded_non_collapsed_types:        0
% 2.27/1.02  num_pure_diseq_elim:                    0
% 2.27/1.02  simp_replaced_by:                       0
% 2.27/1.02  res_preprocessed:                       63
% 2.27/1.02  prep_upred:                             0
% 2.27/1.02  prep_unflattend:                        0
% 2.27/1.02  smt_new_axioms:                         0
% 2.27/1.02  pred_elim_cands:                        3
% 2.27/1.02  pred_elim:                              0
% 2.27/1.02  pred_elim_cl:                           0
% 2.27/1.02  pred_elim_cycles:                       1
% 2.27/1.02  merged_defs:                            12
% 2.27/1.02  merged_defs_ncl:                        0
% 2.27/1.02  bin_hyper_res:                          21
% 2.27/1.02  prep_cycles:                            3
% 2.27/1.02  pred_elim_time:                         0.
% 2.27/1.02  splitting_time:                         0.
% 2.27/1.02  sem_filter_time:                        0.
% 2.27/1.02  monotx_time:                            0.
% 2.27/1.02  subtype_inf_time:                       0.
% 2.27/1.02  
% 2.27/1.02  ------ Problem properties
% 2.27/1.02  
% 2.27/1.02  clauses:                                16
% 2.27/1.02  conjectures:                            4
% 2.27/1.02  epr:                                    2
% 2.27/1.02  horn:                                   13
% 2.27/1.02  ground:                                 4
% 2.27/1.02  unary:                                  4
% 2.27/1.02  binary:                                 4
% 2.27/1.02  lits:                                   41
% 2.27/1.02  lits_eq:                                2
% 2.27/1.02  fd_pure:                                0
% 2.27/1.02  fd_pseudo:                              0
% 2.27/1.02  fd_cond:                                0
% 2.27/1.02  fd_pseudo_cond:                         2
% 2.27/1.02  ac_symbols:                             0
% 2.27/1.02  
% 2.27/1.02  ------ Propositional Solver
% 2.27/1.02  
% 2.27/1.02  prop_solver_calls:                      23
% 2.27/1.02  prop_fast_solver_calls:                 533
% 2.27/1.02  smt_solver_calls:                       0
% 2.27/1.02  smt_fast_solver_calls:                  0
% 2.27/1.02  prop_num_of_clauses:                    1316
% 2.27/1.02  prop_preprocess_simplified:             3434
% 2.27/1.02  prop_fo_subsumed:                       8
% 2.27/1.02  prop_solver_time:                       0.
% 2.27/1.02  smt_solver_time:                        0.
% 2.27/1.02  smt_fast_solver_time:                   0.
% 2.27/1.02  prop_fast_solver_time:                  0.
% 2.27/1.02  prop_unsat_core_time:                   0.
% 2.27/1.02  
% 2.27/1.02  ------ QBF
% 2.27/1.02  
% 2.27/1.02  qbf_q_res:                              0
% 2.27/1.02  qbf_num_tautologies:                    0
% 2.27/1.02  qbf_prep_cycles:                        0
% 2.27/1.02  
% 2.27/1.02  ------ BMC1
% 2.27/1.02  
% 2.27/1.02  bmc1_current_bound:                     -1
% 2.27/1.02  bmc1_last_solved_bound:                 -1
% 2.27/1.02  bmc1_unsat_core_size:                   -1
% 2.27/1.02  bmc1_unsat_core_parents_size:           -1
% 2.27/1.02  bmc1_merge_next_fun:                    0
% 2.27/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.02  
% 2.27/1.02  ------ Instantiation
% 2.27/1.02  
% 2.27/1.02  inst_num_of_clauses:                    367
% 2.27/1.02  inst_num_in_passive:                    65
% 2.27/1.02  inst_num_in_active:                     241
% 2.27/1.02  inst_num_in_unprocessed:                61
% 2.27/1.02  inst_num_of_loops:                      270
% 2.27/1.02  inst_num_of_learning_restarts:          0
% 2.27/1.02  inst_num_moves_active_passive:          26
% 2.27/1.02  inst_lit_activity:                      0
% 2.27/1.02  inst_lit_activity_moves:                0
% 2.27/1.02  inst_num_tautologies:                   0
% 2.27/1.02  inst_num_prop_implied:                  0
% 2.27/1.02  inst_num_existing_simplified:           0
% 2.27/1.02  inst_num_eq_res_simplified:             0
% 2.27/1.02  inst_num_child_elim:                    0
% 2.27/1.02  inst_num_of_dismatching_blockings:      39
% 2.27/1.02  inst_num_of_non_proper_insts:           396
% 2.27/1.02  inst_num_of_duplicates:                 0
% 2.27/1.02  inst_inst_num_from_inst_to_res:         0
% 2.27/1.02  inst_dismatching_checking_time:         0.
% 2.27/1.02  
% 2.27/1.02  ------ Resolution
% 2.27/1.02  
% 2.27/1.02  res_num_of_clauses:                     0
% 2.27/1.02  res_num_in_passive:                     0
% 2.27/1.02  res_num_in_active:                      0
% 2.27/1.02  res_num_of_loops:                       66
% 2.27/1.02  res_forward_subset_subsumed:            33
% 2.27/1.02  res_backward_subset_subsumed:           0
% 2.27/1.02  res_forward_subsumed:                   0
% 2.27/1.02  res_backward_subsumed:                  0
% 2.27/1.02  res_forward_subsumption_resolution:     0
% 2.27/1.02  res_backward_subsumption_resolution:    0
% 2.27/1.02  res_clause_to_clause_subsumption:       594
% 2.27/1.02  res_orphan_elimination:                 0
% 2.27/1.02  res_tautology_del:                      103
% 2.27/1.02  res_num_eq_res_simplified:              0
% 2.27/1.02  res_num_sel_changes:                    0
% 2.27/1.02  res_moves_from_active_to_pass:          0
% 2.27/1.02  
% 2.27/1.02  ------ Superposition
% 2.27/1.02  
% 2.27/1.02  sup_time_total:                         0.
% 2.27/1.02  sup_time_generating:                    0.
% 2.27/1.02  sup_time_sim_full:                      0.
% 2.27/1.02  sup_time_sim_immed:                     0.
% 2.27/1.02  
% 2.27/1.02  sup_num_of_clauses:                     76
% 2.27/1.02  sup_num_in_active:                      54
% 2.27/1.02  sup_num_in_passive:                     22
% 2.27/1.02  sup_num_of_loops:                       53
% 2.27/1.02  sup_fw_superposition:                   44
% 2.27/1.02  sup_bw_superposition:                   52
% 2.27/1.02  sup_immediate_simplified:               22
% 2.27/1.02  sup_given_eliminated:                   0
% 2.27/1.02  comparisons_done:                       0
% 2.27/1.02  comparisons_avoided:                    0
% 2.27/1.02  
% 2.27/1.02  ------ Simplifications
% 2.27/1.02  
% 2.27/1.02  
% 2.27/1.02  sim_fw_subset_subsumed:                 3
% 2.27/1.02  sim_bw_subset_subsumed:                 2
% 2.27/1.02  sim_fw_subsumed:                        15
% 2.27/1.02  sim_bw_subsumed:                        0
% 2.27/1.02  sim_fw_subsumption_res:                 3
% 2.27/1.02  sim_bw_subsumption_res:                 0
% 2.27/1.02  sim_tautology_del:                      9
% 2.27/1.02  sim_eq_tautology_del:                   2
% 2.27/1.02  sim_eq_res_simp:                        1
% 2.27/1.02  sim_fw_demodulated:                     0
% 2.27/1.02  sim_bw_demodulated:                     0
% 2.27/1.02  sim_light_normalised:                   0
% 2.27/1.02  sim_joinable_taut:                      0
% 2.27/1.02  sim_joinable_simp:                      0
% 2.27/1.02  sim_ac_normalised:                      0
% 2.27/1.02  sim_smt_subsumption:                    0
% 2.27/1.02  
%------------------------------------------------------------------------------
