%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0395+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:12 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of clauses        :   29 (  34 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  180 ( 360 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f20,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK1(X1,X4))
        & r2_hidden(sK1(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK0(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK1(X1,X4))
              & r2_hidden(sK1(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK1(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK1(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK2,sK3)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_setfam_1(sK2,sK3)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f23])).

fof(f35,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ~ r1_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : r1_setfam_1(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f29,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(sK0(X2,X1),X0)
    | r1_setfam_1(X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK0(sK2,sK3),X0)
    | r1_setfam_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_884,plain,
    ( ~ r2_hidden(sK1(sK2,sK0(sK2,sK3)),sK3)
    | ~ r1_tarski(sK0(sK2,sK3),sK1(sK2,sK0(sK2,sK3)))
    | r1_setfam_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_93,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_94,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_93])).

cnf(c_120,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_94])).

cnf(c_613,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_678,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_616,plain,
    ( ~ m1_subset_1(sK1(sK2,sK0(sK2,sK3)),sK3)
    | r2_hidden(sK1(sK2,sK0(sK2,sK3)),sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X0,sK0(sK2,sK3)),X1)
    | ~ r2_hidden(sK1(X0,sK0(sK2,sK3)),X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_571,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,sK3)),sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK1(sK2,sK0(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X0),X2)
    | ~ r1_setfam_1(X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_469,plain,
    ( r2_hidden(sK1(X0,sK0(sK2,sK3)),X0)
    | ~ r2_hidden(sK0(sK2,sK3),sK2)
    | ~ r1_setfam_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_476,plain,
    ( r2_hidden(sK1(sK2,sK0(sK2,sK3)),sK2)
    | ~ r2_hidden(sK0(sK2,sK3),sK2)
    | ~ r1_setfam_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,sK1(X2,X0))
    | ~ r1_setfam_1(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_470,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | r1_tarski(sK0(sK2,sK3),sK1(X0,sK0(sK2,sK3)))
    | ~ r1_setfam_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_472,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | r1_tarski(sK0(sK2,sK3),sK1(sK2,sK0(sK2,sK3)))
    | ~ r1_setfam_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_359,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    inference(resolution,[status(thm)],[c_94,c_11])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_setfam_1(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,negated_conjecture,
    ( ~ r1_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_206,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_4,plain,
    ( r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_30,plain,
    ( r1_setfam_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_884,c_678,c_616,c_571,c_476,c_472,c_359,c_206,c_30,c_10,c_11])).


%------------------------------------------------------------------------------
