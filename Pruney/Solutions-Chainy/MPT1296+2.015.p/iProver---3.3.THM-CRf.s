%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:16 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 423 expanded)
%              Number of clauses        :   64 ( 156 expanded)
%              Number of leaves         :   13 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          :  335 (1361 expanded)
%              Number of equality atoms :  153 ( 570 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f32])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | r2_hidden(sK0(X0,X1,X2),X2) )
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | r2_hidden(sK0(X0,X1,X2),X2) )
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_546,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_547,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1276,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
    | k7_setfam_1(X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_547])).

cnf(c_7659,plain,
    ( k6_setfam_1(sK1,k7_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))
    | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_546,c_1276])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_549,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1145,plain,
    ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_546,c_549])).

cnf(c_7662,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0
    | k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k6_setfam_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7659,c_1145])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_551,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_558,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1236,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_558])).

cnf(c_3537,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_1236])).

cnf(c_6261,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_546,c_3537])).

cnf(c_8883,plain,
    ( k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2))
    | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7662,c_6261])).

cnf(c_14,negated_conjecture,
    ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9046,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8883,c_14])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k7_setfam_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_555,plain,
    ( k7_setfam_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_548,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1438,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_548])).

cnf(c_1564,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_558])).

cnf(c_2243,plain,
    ( k7_setfam_1(X0,X1) = sK2
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(X0,X1,sK2))) = sK0(X0,X1,sK2)
    | r2_hidden(k3_subset_1(X0,sK0(X0,X1,sK2)),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_1564])).

cnf(c_2805,plain,
    ( k7_setfam_1(X0,sK2) = sK2
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(X0,sK2,sK2))) = sK0(X0,sK2,sK2)
    | k3_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(X0,sK0(X0,sK2,sK2)))) = k3_subset_1(X0,sK0(X0,sK2,sK2))
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2243,c_1564])).

cnf(c_3086,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
    | k3_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2)))) = k3_subset_1(sK1,sK0(sK1,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_546,c_2805])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | k7_setfam_1(sK1,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_949,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | k7_setfam_1(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_2361,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3724,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
    | k7_setfam_1(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3086,c_16,c_949,c_2361])).

cnf(c_3725,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
    inference(renaming,[status(thm)],[c_3724])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_552,plain,
    ( r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_622,plain,
    ( r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_552,c_550,c_548])).

cnf(c_3129,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),k7_setfam_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_622])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_695,plain,
    ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_696,plain,
    ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_3729,plain,
    ( r2_hidden(k3_subset_1(sK1,X0),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3129,c_17,c_696])).

cnf(c_3730,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),k7_setfam_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3729])).

cnf(c_3739,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3725,c_3730])).

cnf(c_4225,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_3739])).

cnf(c_5986,plain,
    ( r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
    | k7_setfam_1(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4225,c_17])).

cnf(c_5987,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5986])).

cnf(c_9068,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9046,c_5987])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_557,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_181,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_545,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_927,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_545])).

cnf(c_9079,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9046,c_3730])).

cnf(c_9667,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9079,c_927])).

cnf(c_10064,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9068,c_927,c_9667])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10095,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10064,c_15])).

cnf(c_10096,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10095])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n012.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 13:22:37 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 3.78/0.95  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/0.95  
% 3.78/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.95  
% 3.78/0.95  ------  iProver source info
% 3.78/0.95  
% 3.78/0.95  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.95  git: non_committed_changes: false
% 3.78/0.95  git: last_make_outside_of_git: false
% 3.78/0.95  
% 3.78/0.95  ------ 
% 3.78/0.95  
% 3.78/0.95  ------ Input Options
% 3.78/0.95  
% 3.78/0.95  --out_options                           all
% 3.78/0.95  --tptp_safe_out                         true
% 3.78/0.95  --problem_path                          ""
% 3.78/0.95  --include_path                          ""
% 3.78/0.95  --clausifier                            res/vclausify_rel
% 3.78/0.95  --clausifier_options                    --mode clausify
% 3.78/0.95  --stdin                                 false
% 3.78/0.95  --stats_out                             all
% 3.78/0.95  
% 3.78/0.95  ------ General Options
% 3.78/0.95  
% 3.78/0.95  --fof                                   false
% 3.78/0.95  --time_out_real                         305.
% 3.78/0.95  --time_out_virtual                      -1.
% 3.78/0.95  --symbol_type_check                     false
% 3.78/0.95  --clausify_out                          false
% 3.78/0.95  --sig_cnt_out                           false
% 3.78/0.95  --trig_cnt_out                          false
% 3.78/0.95  --trig_cnt_out_tolerance                1.
% 3.78/0.95  --trig_cnt_out_sk_spl                   false
% 3.78/0.95  --abstr_cl_out                          false
% 3.78/0.95  
% 3.78/0.95  ------ Global Options
% 3.78/0.95  
% 3.78/0.95  --schedule                              default
% 3.78/0.95  --add_important_lit                     false
% 3.78/0.95  --prop_solver_per_cl                    1000
% 3.78/0.95  --min_unsat_core                        false
% 3.78/0.95  --soft_assumptions                      false
% 3.78/0.95  --soft_lemma_size                       3
% 3.78/0.95  --prop_impl_unit_size                   0
% 3.78/0.95  --prop_impl_unit                        []
% 3.78/0.95  --share_sel_clauses                     true
% 3.78/0.95  --reset_solvers                         false
% 3.78/0.95  --bc_imp_inh                            [conj_cone]
% 3.78/0.95  --conj_cone_tolerance                   3.
% 3.78/0.95  --extra_neg_conj                        none
% 3.78/0.95  --large_theory_mode                     true
% 3.78/0.95  --prolific_symb_bound                   200
% 3.78/0.95  --lt_threshold                          2000
% 3.78/0.95  --clause_weak_htbl                      true
% 3.78/0.95  --gc_record_bc_elim                     false
% 3.78/0.95  
% 3.78/0.95  ------ Preprocessing Options
% 3.78/0.95  
% 3.78/0.95  --preprocessing_flag                    true
% 3.78/0.95  --time_out_prep_mult                    0.1
% 3.78/0.95  --splitting_mode                        input
% 3.78/0.95  --splitting_grd                         true
% 3.78/0.95  --splitting_cvd                         false
% 3.78/0.95  --splitting_cvd_svl                     false
% 3.78/0.95  --splitting_nvd                         32
% 3.78/0.95  --sub_typing                            true
% 3.78/0.95  --prep_gs_sim                           true
% 3.78/0.95  --prep_unflatten                        true
% 3.78/0.95  --prep_res_sim                          true
% 3.78/0.95  --prep_upred                            true
% 3.78/0.95  --prep_sem_filter                       exhaustive
% 3.78/0.95  --prep_sem_filter_out                   false
% 3.78/0.95  --pred_elim                             true
% 3.78/0.95  --res_sim_input                         true
% 3.78/0.95  --eq_ax_congr_red                       true
% 3.78/0.95  --pure_diseq_elim                       true
% 3.78/0.95  --brand_transform                       false
% 3.78/0.95  --non_eq_to_eq                          false
% 3.78/0.95  --prep_def_merge                        true
% 3.78/0.95  --prep_def_merge_prop_impl              false
% 3.78/0.95  --prep_def_merge_mbd                    true
% 3.78/0.95  --prep_def_merge_tr_red                 false
% 3.78/0.95  --prep_def_merge_tr_cl                  false
% 3.78/0.95  --smt_preprocessing                     true
% 3.78/0.95  --smt_ac_axioms                         fast
% 3.78/0.95  --preprocessed_out                      false
% 3.78/0.95  --preprocessed_stats                    false
% 3.78/0.95  
% 3.78/0.95  ------ Abstraction refinement Options
% 3.78/0.95  
% 3.78/0.95  --abstr_ref                             []
% 3.78/0.95  --abstr_ref_prep                        false
% 3.78/0.95  --abstr_ref_until_sat                   false
% 3.78/0.95  --abstr_ref_sig_restrict                funpre
% 3.78/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.95  --abstr_ref_under                       []
% 3.78/0.95  
% 3.78/0.95  ------ SAT Options
% 3.78/0.95  
% 3.78/0.95  --sat_mode                              false
% 3.78/0.95  --sat_fm_restart_options                ""
% 3.78/0.95  --sat_gr_def                            false
% 3.78/0.95  --sat_epr_types                         true
% 3.78/0.95  --sat_non_cyclic_types                  false
% 3.78/0.95  --sat_finite_models                     false
% 3.78/0.95  --sat_fm_lemmas                         false
% 3.78/0.95  --sat_fm_prep                           false
% 4.02/0.95  --sat_fm_uc_incr                        true
% 4.02/0.95  --sat_out_model                         small
% 4.02/0.95  --sat_out_clauses                       false
% 4.02/0.95  
% 4.02/0.95  ------ QBF Options
% 4.02/0.95  
% 4.02/0.95  --qbf_mode                              false
% 4.02/0.95  --qbf_elim_univ                         false
% 4.02/0.95  --qbf_dom_inst                          none
% 4.02/0.95  --qbf_dom_pre_inst                      false
% 4.02/0.95  --qbf_sk_in                             false
% 4.02/0.95  --qbf_pred_elim                         true
% 4.02/0.95  --qbf_split                             512
% 4.02/0.95  
% 4.02/0.95  ------ BMC1 Options
% 4.02/0.95  
% 4.02/0.95  --bmc1_incremental                      false
% 4.02/0.95  --bmc1_axioms                           reachable_all
% 4.02/0.95  --bmc1_min_bound                        0
% 4.02/0.95  --bmc1_max_bound                        -1
% 4.02/0.95  --bmc1_max_bound_default                -1
% 4.02/0.95  --bmc1_symbol_reachability              true
% 4.02/0.95  --bmc1_property_lemmas                  false
% 4.02/0.95  --bmc1_k_induction                      false
% 4.02/0.95  --bmc1_non_equiv_states                 false
% 4.02/0.95  --bmc1_deadlock                         false
% 4.02/0.95  --bmc1_ucm                              false
% 4.02/0.95  --bmc1_add_unsat_core                   none
% 4.02/0.95  --bmc1_unsat_core_children              false
% 4.02/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.95  --bmc1_out_stat                         full
% 4.02/0.95  --bmc1_ground_init                      false
% 4.02/0.95  --bmc1_pre_inst_next_state              false
% 4.02/0.95  --bmc1_pre_inst_state                   false
% 4.02/0.95  --bmc1_pre_inst_reach_state             false
% 4.02/0.95  --bmc1_out_unsat_core                   false
% 4.02/0.95  --bmc1_aig_witness_out                  false
% 4.02/0.95  --bmc1_verbose                          false
% 4.02/0.95  --bmc1_dump_clauses_tptp                false
% 4.02/0.95  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.95  --bmc1_dump_file                        -
% 4.02/0.95  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.95  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.95  --bmc1_ucm_extend_mode                  1
% 4.02/0.95  --bmc1_ucm_init_mode                    2
% 4.02/0.95  --bmc1_ucm_cone_mode                    none
% 4.02/0.95  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.95  --bmc1_ucm_relax_model                  4
% 4.02/0.95  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.95  --bmc1_ucm_layered_model                none
% 4.02/0.95  --bmc1_ucm_max_lemma_size               10
% 4.02/0.95  
% 4.02/0.95  ------ AIG Options
% 4.02/0.95  
% 4.02/0.95  --aig_mode                              false
% 4.02/0.95  
% 4.02/0.95  ------ Instantiation Options
% 4.02/0.95  
% 4.02/0.95  --instantiation_flag                    true
% 4.02/0.95  --inst_sos_flag                         false
% 4.02/0.95  --inst_sos_phase                        true
% 4.02/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.95  --inst_lit_sel_side                     num_symb
% 4.02/0.95  --inst_solver_per_active                1400
% 4.02/0.95  --inst_solver_calls_frac                1.
% 4.02/0.95  --inst_passive_queue_type               priority_queues
% 4.02/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.95  --inst_passive_queues_freq              [25;2]
% 4.02/0.95  --inst_dismatching                      true
% 4.02/0.95  --inst_eager_unprocessed_to_passive     true
% 4.02/0.95  --inst_prop_sim_given                   true
% 4.02/0.95  --inst_prop_sim_new                     false
% 4.02/0.95  --inst_subs_new                         false
% 4.02/0.95  --inst_eq_res_simp                      false
% 4.02/0.95  --inst_subs_given                       false
% 4.02/0.95  --inst_orphan_elimination               true
% 4.02/0.95  --inst_learning_loop_flag               true
% 4.02/0.95  --inst_learning_start                   3000
% 4.02/0.95  --inst_learning_factor                  2
% 4.02/0.95  --inst_start_prop_sim_after_learn       3
% 4.02/0.95  --inst_sel_renew                        solver
% 4.02/0.95  --inst_lit_activity_flag                true
% 4.02/0.95  --inst_restr_to_given                   false
% 4.02/0.95  --inst_activity_threshold               500
% 4.02/0.95  --inst_out_proof                        true
% 4.02/0.95  
% 4.02/0.95  ------ Resolution Options
% 4.02/0.95  
% 4.02/0.95  --resolution_flag                       true
% 4.02/0.95  --res_lit_sel                           adaptive
% 4.02/0.95  --res_lit_sel_side                      none
% 4.02/0.95  --res_ordering                          kbo
% 4.02/0.95  --res_to_prop_solver                    active
% 4.02/0.95  --res_prop_simpl_new                    false
% 4.02/0.95  --res_prop_simpl_given                  true
% 4.02/0.95  --res_passive_queue_type                priority_queues
% 4.02/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.95  --res_passive_queues_freq               [15;5]
% 4.02/0.95  --res_forward_subs                      full
% 4.02/0.95  --res_backward_subs                     full
% 4.02/0.95  --res_forward_subs_resolution           true
% 4.02/0.95  --res_backward_subs_resolution          true
% 4.02/0.95  --res_orphan_elimination                true
% 4.02/0.95  --res_time_limit                        2.
% 4.02/0.95  --res_out_proof                         true
% 4.02/0.95  
% 4.02/0.95  ------ Superposition Options
% 4.02/0.95  
% 4.02/0.95  --superposition_flag                    true
% 4.02/0.95  --sup_passive_queue_type                priority_queues
% 4.02/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.95  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.95  --demod_completeness_check              fast
% 4.02/0.95  --demod_use_ground                      true
% 4.02/0.95  --sup_to_prop_solver                    passive
% 4.02/0.95  --sup_prop_simpl_new                    true
% 4.02/0.95  --sup_prop_simpl_given                  true
% 4.02/0.95  --sup_fun_splitting                     false
% 4.02/0.95  --sup_smt_interval                      50000
% 4.02/0.95  
% 4.02/0.95  ------ Superposition Simplification Setup
% 4.02/0.95  
% 4.02/0.95  --sup_indices_passive                   []
% 4.02/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.95  --sup_full_bw                           [BwDemod]
% 4.02/0.95  --sup_immed_triv                        [TrivRules]
% 4.02/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.95  --sup_immed_bw_main                     []
% 4.02/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.95  
% 4.02/0.95  ------ Combination Options
% 4.02/0.95  
% 4.02/0.95  --comb_res_mult                         3
% 4.02/0.95  --comb_sup_mult                         2
% 4.02/0.95  --comb_inst_mult                        10
% 4.02/0.95  
% 4.02/0.95  ------ Debug Options
% 4.02/0.95  
% 4.02/0.95  --dbg_backtrace                         false
% 4.02/0.95  --dbg_dump_prop_clauses                 false
% 4.02/0.95  --dbg_dump_prop_clauses_file            -
% 4.02/0.95  --dbg_out_stat                          false
% 4.02/0.95  ------ Parsing...
% 4.02/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.95  
% 4.02/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.02/0.95  
% 4.02/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.95  
% 4.02/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.95  ------ Proving...
% 4.02/0.95  ------ Problem Properties 
% 4.02/0.95  
% 4.02/0.95  
% 4.02/0.95  clauses                                 16
% 4.02/0.95  conjectures                             3
% 4.02/0.95  EPR                                     1
% 4.02/0.95  Horn                                    13
% 4.02/0.95  unary                                   4
% 4.02/0.95  binary                                  5
% 4.02/0.95  lits                                    44
% 4.02/0.95  lits eq                                 9
% 4.02/0.95  fd_pure                                 0
% 4.02/0.95  fd_pseudo                               0
% 4.02/0.95  fd_cond                                 1
% 4.02/0.95  fd_pseudo_cond                          3
% 4.02/0.95  AC symbols                              0
% 4.02/0.95  
% 4.02/0.95  ------ Schedule dynamic 5 is on 
% 4.02/0.95  
% 4.02/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.02/0.95  
% 4.02/0.95  
% 4.02/0.95  ------ 
% 4.02/0.95  Current options:
% 4.02/0.95  ------ 
% 4.02/0.95  
% 4.02/0.95  ------ Input Options
% 4.02/0.95  
% 4.02/0.95  --out_options                           all
% 4.02/0.95  --tptp_safe_out                         true
% 4.02/0.95  --problem_path                          ""
% 4.02/0.95  --include_path                          ""
% 4.02/0.95  --clausifier                            res/vclausify_rel
% 4.02/0.95  --clausifier_options                    --mode clausify
% 4.02/0.95  --stdin                                 false
% 4.02/0.95  --stats_out                             all
% 4.02/0.95  
% 4.02/0.95  ------ General Options
% 4.02/0.95  
% 4.02/0.95  --fof                                   false
% 4.02/0.95  --time_out_real                         305.
% 4.02/0.95  --time_out_virtual                      -1.
% 4.02/0.95  --symbol_type_check                     false
% 4.02/0.95  --clausify_out                          false
% 4.02/0.95  --sig_cnt_out                           false
% 4.02/0.95  --trig_cnt_out                          false
% 4.02/0.95  --trig_cnt_out_tolerance                1.
% 4.02/0.95  --trig_cnt_out_sk_spl                   false
% 4.02/0.95  --abstr_cl_out                          false
% 4.02/0.95  
% 4.02/0.95  ------ Global Options
% 4.02/0.95  
% 4.02/0.95  --schedule                              default
% 4.02/0.95  --add_important_lit                     false
% 4.02/0.95  --prop_solver_per_cl                    1000
% 4.02/0.95  --min_unsat_core                        false
% 4.02/0.95  --soft_assumptions                      false
% 4.02/0.95  --soft_lemma_size                       3
% 4.02/0.95  --prop_impl_unit_size                   0
% 4.02/0.95  --prop_impl_unit                        []
% 4.02/0.95  --share_sel_clauses                     true
% 4.02/0.95  --reset_solvers                         false
% 4.02/0.95  --bc_imp_inh                            [conj_cone]
% 4.02/0.95  --conj_cone_tolerance                   3.
% 4.02/0.95  --extra_neg_conj                        none
% 4.02/0.95  --large_theory_mode                     true
% 4.02/0.95  --prolific_symb_bound                   200
% 4.02/0.95  --lt_threshold                          2000
% 4.02/0.95  --clause_weak_htbl                      true
% 4.02/0.95  --gc_record_bc_elim                     false
% 4.02/0.95  
% 4.02/0.95  ------ Preprocessing Options
% 4.02/0.95  
% 4.02/0.95  --preprocessing_flag                    true
% 4.02/0.95  --time_out_prep_mult                    0.1
% 4.02/0.95  --splitting_mode                        input
% 4.02/0.95  --splitting_grd                         true
% 4.02/0.95  --splitting_cvd                         false
% 4.02/0.95  --splitting_cvd_svl                     false
% 4.02/0.95  --splitting_nvd                         32
% 4.02/0.95  --sub_typing                            true
% 4.02/0.95  --prep_gs_sim                           true
% 4.02/0.95  --prep_unflatten                        true
% 4.02/0.95  --prep_res_sim                          true
% 4.02/0.95  --prep_upred                            true
% 4.02/0.95  --prep_sem_filter                       exhaustive
% 4.02/0.95  --prep_sem_filter_out                   false
% 4.02/0.95  --pred_elim                             true
% 4.02/0.95  --res_sim_input                         true
% 4.02/0.95  --eq_ax_congr_red                       true
% 4.02/0.95  --pure_diseq_elim                       true
% 4.02/0.95  --brand_transform                       false
% 4.02/0.95  --non_eq_to_eq                          false
% 4.02/0.95  --prep_def_merge                        true
% 4.02/0.95  --prep_def_merge_prop_impl              false
% 4.02/0.95  --prep_def_merge_mbd                    true
% 4.02/0.95  --prep_def_merge_tr_red                 false
% 4.02/0.95  --prep_def_merge_tr_cl                  false
% 4.02/0.95  --smt_preprocessing                     true
% 4.02/0.95  --smt_ac_axioms                         fast
% 4.02/0.95  --preprocessed_out                      false
% 4.02/0.95  --preprocessed_stats                    false
% 4.02/0.95  
% 4.02/0.95  ------ Abstraction refinement Options
% 4.02/0.95  
% 4.02/0.95  --abstr_ref                             []
% 4.02/0.95  --abstr_ref_prep                        false
% 4.02/0.95  --abstr_ref_until_sat                   false
% 4.02/0.95  --abstr_ref_sig_restrict                funpre
% 4.02/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.95  --abstr_ref_under                       []
% 4.02/0.95  
% 4.02/0.95  ------ SAT Options
% 4.02/0.95  
% 4.02/0.95  --sat_mode                              false
% 4.02/0.95  --sat_fm_restart_options                ""
% 4.02/0.95  --sat_gr_def                            false
% 4.02/0.95  --sat_epr_types                         true
% 4.02/0.95  --sat_non_cyclic_types                  false
% 4.02/0.95  --sat_finite_models                     false
% 4.02/0.95  --sat_fm_lemmas                         false
% 4.02/0.95  --sat_fm_prep                           false
% 4.02/0.95  --sat_fm_uc_incr                        true
% 4.02/0.95  --sat_out_model                         small
% 4.02/0.95  --sat_out_clauses                       false
% 4.02/0.95  
% 4.02/0.95  ------ QBF Options
% 4.02/0.95  
% 4.02/0.95  --qbf_mode                              false
% 4.02/0.95  --qbf_elim_univ                         false
% 4.02/0.95  --qbf_dom_inst                          none
% 4.02/0.95  --qbf_dom_pre_inst                      false
% 4.02/0.95  --qbf_sk_in                             false
% 4.02/0.95  --qbf_pred_elim                         true
% 4.02/0.95  --qbf_split                             512
% 4.02/0.95  
% 4.02/0.95  ------ BMC1 Options
% 4.02/0.95  
% 4.02/0.95  --bmc1_incremental                      false
% 4.02/0.95  --bmc1_axioms                           reachable_all
% 4.02/0.95  --bmc1_min_bound                        0
% 4.02/0.95  --bmc1_max_bound                        -1
% 4.02/0.95  --bmc1_max_bound_default                -1
% 4.02/0.95  --bmc1_symbol_reachability              true
% 4.02/0.95  --bmc1_property_lemmas                  false
% 4.02/0.95  --bmc1_k_induction                      false
% 4.02/0.95  --bmc1_non_equiv_states                 false
% 4.02/0.95  --bmc1_deadlock                         false
% 4.02/0.95  --bmc1_ucm                              false
% 4.02/0.95  --bmc1_add_unsat_core                   none
% 4.02/0.95  --bmc1_unsat_core_children              false
% 4.02/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.95  --bmc1_out_stat                         full
% 4.02/0.95  --bmc1_ground_init                      false
% 4.02/0.95  --bmc1_pre_inst_next_state              false
% 4.02/0.95  --bmc1_pre_inst_state                   false
% 4.02/0.95  --bmc1_pre_inst_reach_state             false
% 4.02/0.95  --bmc1_out_unsat_core                   false
% 4.02/0.95  --bmc1_aig_witness_out                  false
% 4.02/0.95  --bmc1_verbose                          false
% 4.02/0.95  --bmc1_dump_clauses_tptp                false
% 4.02/0.95  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.95  --bmc1_dump_file                        -
% 4.02/0.95  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.95  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.95  --bmc1_ucm_extend_mode                  1
% 4.02/0.95  --bmc1_ucm_init_mode                    2
% 4.02/0.95  --bmc1_ucm_cone_mode                    none
% 4.02/0.95  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.95  --bmc1_ucm_relax_model                  4
% 4.02/0.95  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.95  --bmc1_ucm_layered_model                none
% 4.02/0.95  --bmc1_ucm_max_lemma_size               10
% 4.02/0.95  
% 4.02/0.95  ------ AIG Options
% 4.02/0.95  
% 4.02/0.95  --aig_mode                              false
% 4.02/0.95  
% 4.02/0.95  ------ Instantiation Options
% 4.02/0.95  
% 4.02/0.95  --instantiation_flag                    true
% 4.02/0.95  --inst_sos_flag                         false
% 4.02/0.95  --inst_sos_phase                        true
% 4.02/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.95  --inst_lit_sel_side                     none
% 4.02/0.95  --inst_solver_per_active                1400
% 4.02/0.95  --inst_solver_calls_frac                1.
% 4.02/0.95  --inst_passive_queue_type               priority_queues
% 4.02/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.95  --inst_passive_queues_freq              [25;2]
% 4.02/0.95  --inst_dismatching                      true
% 4.02/0.95  --inst_eager_unprocessed_to_passive     true
% 4.02/0.95  --inst_prop_sim_given                   true
% 4.02/0.95  --inst_prop_sim_new                     false
% 4.02/0.95  --inst_subs_new                         false
% 4.02/0.95  --inst_eq_res_simp                      false
% 4.02/0.95  --inst_subs_given                       false
% 4.02/0.95  --inst_orphan_elimination               true
% 4.02/0.95  --inst_learning_loop_flag               true
% 4.02/0.95  --inst_learning_start                   3000
% 4.02/0.95  --inst_learning_factor                  2
% 4.02/0.95  --inst_start_prop_sim_after_learn       3
% 4.02/0.95  --inst_sel_renew                        solver
% 4.02/0.95  --inst_lit_activity_flag                true
% 4.02/0.95  --inst_restr_to_given                   false
% 4.02/0.95  --inst_activity_threshold               500
% 4.02/0.95  --inst_out_proof                        true
% 4.02/0.95  
% 4.02/0.95  ------ Resolution Options
% 4.02/0.95  
% 4.02/0.95  --resolution_flag                       false
% 4.02/0.95  --res_lit_sel                           adaptive
% 4.02/0.95  --res_lit_sel_side                      none
% 4.02/0.95  --res_ordering                          kbo
% 4.02/0.95  --res_to_prop_solver                    active
% 4.02/0.95  --res_prop_simpl_new                    false
% 4.02/0.95  --res_prop_simpl_given                  true
% 4.02/0.95  --res_passive_queue_type                priority_queues
% 4.02/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.95  --res_passive_queues_freq               [15;5]
% 4.02/0.95  --res_forward_subs                      full
% 4.02/0.95  --res_backward_subs                     full
% 4.02/0.95  --res_forward_subs_resolution           true
% 4.02/0.95  --res_backward_subs_resolution          true
% 4.02/0.95  --res_orphan_elimination                true
% 4.02/0.95  --res_time_limit                        2.
% 4.02/0.95  --res_out_proof                         true
% 4.02/0.95  
% 4.02/0.95  ------ Superposition Options
% 4.02/0.95  
% 4.02/0.95  --superposition_flag                    true
% 4.02/0.95  --sup_passive_queue_type                priority_queues
% 4.02/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.95  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.95  --demod_completeness_check              fast
% 4.02/0.95  --demod_use_ground                      true
% 4.02/0.95  --sup_to_prop_solver                    passive
% 4.02/0.95  --sup_prop_simpl_new                    true
% 4.02/0.95  --sup_prop_simpl_given                  true
% 4.02/0.95  --sup_fun_splitting                     false
% 4.02/0.95  --sup_smt_interval                      50000
% 4.02/0.95  
% 4.02/0.95  ------ Superposition Simplification Setup
% 4.02/0.95  
% 4.02/0.95  --sup_indices_passive                   []
% 4.02/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.95  --sup_full_bw                           [BwDemod]
% 4.02/0.95  --sup_immed_triv                        [TrivRules]
% 4.02/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.95  --sup_immed_bw_main                     []
% 4.02/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.02/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.02/0.95  
% 4.02/0.95  ------ Combination Options
% 4.02/0.95  
% 4.02/0.95  --comb_res_mult                         3
% 4.02/0.95  --comb_sup_mult                         2
% 4.02/0.95  --comb_inst_mult                        10
% 4.02/0.95  
% 4.02/0.95  ------ Debug Options
% 4.02/0.95  
% 4.02/0.95  --dbg_backtrace                         false
% 4.02/0.95  --dbg_dump_prop_clauses                 false
% 4.02/0.95  --dbg_dump_prop_clauses_file            -
% 4.02/0.95  --dbg_out_stat                          false
% 4.02/0.95  
% 4.02/0.95  
% 4.02/0.95  
% 4.02/0.95  
% 4.02/0.95  ------ Proving...
% 4.02/0.95  
% 4.02/0.95  
% 4.02/0.95  % SZS status Theorem for theBenchmark.p
% 4.02/0.95  
% 4.02/0.95   Resolution empty clause
% 4.02/0.95  
% 4.02/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.95  
% 4.02/0.95  fof(f11,conjecture,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f12,negated_conjecture,(
% 4.02/0.95    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 4.02/0.95    inference(negated_conjecture,[],[f11])).
% 4.02/0.95  
% 4.02/0.95  fof(f25,plain,(
% 4.02/0.95    ? [X0,X1] : ((k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(ennf_transformation,[],[f12])).
% 4.02/0.95  
% 4.02/0.95  fof(f26,plain,(
% 4.02/0.95    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(flattening,[],[f25])).
% 4.02/0.95  
% 4.02/0.95  fof(f32,plain,(
% 4.02/0.95    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 4.02/0.95    introduced(choice_axiom,[])).
% 4.02/0.95  
% 4.02/0.95  fof(f33,plain,(
% 4.02/0.95    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 4.02/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f32])).
% 4.02/0.95  
% 4.02/0.95  fof(f48,plain,(
% 4.02/0.95    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 4.02/0.95    inference(cnf_transformation,[],[f33])).
% 4.02/0.95  
% 4.02/0.95  fof(f5,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f17,plain,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(ennf_transformation,[],[f5])).
% 4.02/0.95  
% 4.02/0.95  fof(f42,plain,(
% 4.02/0.95    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f17])).
% 4.02/0.95  
% 4.02/0.95  fof(f10,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f23,plain,(
% 4.02/0.95    ! [X0,X1] : ((k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(ennf_transformation,[],[f10])).
% 4.02/0.95  
% 4.02/0.95  fof(f24,plain,(
% 4.02/0.95    ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(flattening,[],[f23])).
% 4.02/0.95  
% 4.02/0.95  fof(f47,plain,(
% 4.02/0.95    ( ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f24])).
% 4.02/0.95  
% 4.02/0.95  fof(f6,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f18,plain,(
% 4.02/0.95    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(ennf_transformation,[],[f6])).
% 4.02/0.95  
% 4.02/0.95  fof(f43,plain,(
% 4.02/0.95    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f18])).
% 4.02/0.95  
% 4.02/0.95  fof(f4,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f16,plain,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(ennf_transformation,[],[f4])).
% 4.02/0.95  
% 4.02/0.95  fof(f41,plain,(
% 4.02/0.95    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f16])).
% 4.02/0.95  
% 4.02/0.95  fof(f1,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f14,plain,(
% 4.02/0.95    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.95    inference(ennf_transformation,[],[f1])).
% 4.02/0.95  
% 4.02/0.95  fof(f34,plain,(
% 4.02/0.95    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f14])).
% 4.02/0.95  
% 4.02/0.95  fof(f50,plain,(
% 4.02/0.95    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))),
% 4.02/0.95    inference(cnf_transformation,[],[f33])).
% 4.02/0.95  
% 4.02/0.95  fof(f3,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f15,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(ennf_transformation,[],[f3])).
% 4.02/0.95  
% 4.02/0.95  fof(f27,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(nnf_transformation,[],[f15])).
% 4.02/0.95  
% 4.02/0.95  fof(f28,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(flattening,[],[f27])).
% 4.02/0.95  
% 4.02/0.95  fof(f29,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(rectify,[],[f28])).
% 4.02/0.95  
% 4.02/0.95  fof(f30,plain,(
% 4.02/0.95    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))))),
% 4.02/0.95    introduced(choice_axiom,[])).
% 4.02/0.95  
% 4.02/0.95  fof(f31,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.02/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 4.02/0.95  
% 4.02/0.95  fof(f39,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f31])).
% 4.02/0.95  
% 4.02/0.95  fof(f8,axiom,(
% 4.02/0.95    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f20,plain,(
% 4.02/0.95    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 4.02/0.95    inference(ennf_transformation,[],[f8])).
% 4.02/0.95  
% 4.02/0.95  fof(f21,plain,(
% 4.02/0.95    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.02/0.95    inference(flattening,[],[f20])).
% 4.02/0.95  
% 4.02/0.95  fof(f45,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.02/0.95    inference(cnf_transformation,[],[f21])).
% 4.02/0.95  
% 4.02/0.95  fof(f38,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f31])).
% 4.02/0.95  
% 4.02/0.95  fof(f36,plain,(
% 4.02/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f31])).
% 4.02/0.95  
% 4.02/0.95  fof(f52,plain,(
% 4.02/0.95    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 4.02/0.95    inference(equality_resolution,[],[f36])).
% 4.02/0.95  
% 4.02/0.95  fof(f2,axiom,(
% 4.02/0.95    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f35,plain,(
% 4.02/0.95    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f2])).
% 4.02/0.95  
% 4.02/0.95  fof(f7,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f13,plain,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 4.02/0.95    inference(unused_predicate_definition_removal,[],[f7])).
% 4.02/0.95  
% 4.02/0.95  fof(f19,plain,(
% 4.02/0.95    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 4.02/0.95    inference(ennf_transformation,[],[f13])).
% 4.02/0.95  
% 4.02/0.95  fof(f44,plain,(
% 4.02/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f19])).
% 4.02/0.95  
% 4.02/0.95  fof(f9,axiom,(
% 4.02/0.95    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.02/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f22,plain,(
% 4.02/0.95    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.02/0.95    inference(ennf_transformation,[],[f9])).
% 4.02/0.95  
% 4.02/0.95  fof(f46,plain,(
% 4.02/0.95    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.02/0.95    inference(cnf_transformation,[],[f22])).
% 4.02/0.95  
% 4.02/0.95  fof(f49,plain,(
% 4.02/0.95    k1_xboole_0 != sK2),
% 4.02/0.95    inference(cnf_transformation,[],[f33])).
% 4.02/0.95  
% 4.02/0.95  cnf(c_16,negated_conjecture,
% 4.02/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 4.02/0.95      inference(cnf_transformation,[],[f48]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_546,plain,
% 4.02/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_8,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 4.02/0.95      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 4.02/0.95      inference(cnf_transformation,[],[f42]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_550,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 4.02/0.95      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_13,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 4.02/0.95      | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
% 4.02/0.95      | k1_xboole_0 = X0 ),
% 4.02/0.95      inference(cnf_transformation,[],[f47]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_547,plain,
% 4.02/0.95      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
% 4.02/0.95      | k1_xboole_0 = X1
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_1276,plain,
% 4.02/0.95      ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
% 4.02/0.95      | k7_setfam_1(X0,X1) = k1_xboole_0
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_550,c_547]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_7659,plain,
% 4.02/0.95      ( k6_setfam_1(sK1,k7_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))
% 4.02/0.95      | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_546,c_1276]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_9,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 4.02/0.95      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 4.02/0.95      inference(cnf_transformation,[],[f43]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_549,plain,
% 4.02/0.95      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_1145,plain,
% 4.02/0.95      ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_546,c_549]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_7662,plain,
% 4.02/0.95      ( k7_setfam_1(sK1,sK2) = k1_xboole_0
% 4.02/0.95      | k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k6_setfam_1(sK1,sK2) ),
% 4.02/0.95      inference(light_normalisation,[status(thm)],[c_7659,c_1145]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_7,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 4.02/0.95      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.02/0.95      inference(cnf_transformation,[],[f41]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_551,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 4.02/0.95      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_0,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 4.02/0.95      inference(cnf_transformation,[],[f34]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_558,plain,
% 4.02/0.95      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_1236,plain,
% 4.02/0.96      ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
% 4.02/0.96      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_551,c_558]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3537,plain,
% 4.02/0.96      ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
% 4.02/0.96      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_550,c_1236]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_6261,plain,
% 4.02/0.96      ( k3_subset_1(sK1,k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_546,c_3537]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_8883,plain,
% 4.02/0.96      ( k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2))
% 4.02/0.96      | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_7662,c_6261]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_14,negated_conjecture,
% 4.02/0.96      ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
% 4.02/0.96      inference(cnf_transformation,[],[f50]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_9046,plain,
% 4.02/0.96      ( k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_8883,c_14]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3,plain,
% 4.02/0.96      ( r2_hidden(sK0(X0,X1,X2),X2)
% 4.02/0.96      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
% 4.02/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 4.02/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 4.02/0.96      | k7_setfam_1(X0,X1) = X2 ),
% 4.02/0.96      inference(cnf_transformation,[],[f39]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_555,plain,
% 4.02/0.96      ( k7_setfam_1(X0,X1) = X2
% 4.02/0.96      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 4.02/0.96      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top
% 4.02/0.96      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 4.02/0.96      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_11,plain,
% 4.02/0.96      ( ~ r2_hidden(X0,X1)
% 4.02/0.96      | m1_subset_1(X0,X2)
% 4.02/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 4.02/0.96      inference(cnf_transformation,[],[f45]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_548,plain,
% 4.02/0.96      ( r2_hidden(X0,X1) != iProver_top
% 4.02/0.96      | m1_subset_1(X0,X2) = iProver_top
% 4.02/0.96      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_1438,plain,
% 4.02/0.96      ( r2_hidden(X0,sK2) != iProver_top
% 4.02/0.96      | m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_546,c_548]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_1564,plain,
% 4.02/0.96      ( k3_subset_1(sK1,k3_subset_1(sK1,X0)) = X0
% 4.02/0.96      | r2_hidden(X0,sK2) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_1438,c_558]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_2243,plain,
% 4.02/0.96      ( k7_setfam_1(X0,X1) = sK2
% 4.02/0.96      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(X0,X1,sK2))) = sK0(X0,X1,sK2)
% 4.02/0.96      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,sK2)),X1) = iProver_top
% 4.02/0.96      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 4.02/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_555,c_1564]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_2805,plain,
% 4.02/0.96      ( k7_setfam_1(X0,sK2) = sK2
% 4.02/0.96      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(X0,sK2,sK2))) = sK0(X0,sK2,sK2)
% 4.02/0.96      | k3_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(X0,sK0(X0,sK2,sK2)))) = k3_subset_1(X0,sK0(X0,sK2,sK2))
% 4.02/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_2243,c_1564]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3086,plain,
% 4.02/0.96      ( k7_setfam_1(sK1,sK2) = sK2
% 4.02/0.96      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
% 4.02/0.96      | k3_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2)))) = k3_subset_1(sK1,sK0(sK1,sK2,sK2)) ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_546,c_2805]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_4,plain,
% 4.02/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 4.02/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 4.02/0.96      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
% 4.02/0.96      | k7_setfam_1(X1,X2) = X0 ),
% 4.02/0.96      inference(cnf_transformation,[],[f38]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_734,plain,
% 4.02/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 4.02/0.96      | m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
% 4.02/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 4.02/0.96      | k7_setfam_1(sK1,X0) = sK2 ),
% 4.02/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_949,plain,
% 4.02/0.96      ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
% 4.02/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 4.02/0.96      | k7_setfam_1(sK1,sK2) = sK2 ),
% 4.02/0.96      inference(instantiation,[status(thm)],[c_734]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_2361,plain,
% 4.02/0.96      ( ~ m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
% 4.02/0.96      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
% 4.02/0.96      inference(instantiation,[status(thm)],[c_0]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3724,plain,
% 4.02/0.96      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
% 4.02/0.96      | k7_setfam_1(sK1,sK2) = sK2 ),
% 4.02/0.96      inference(global_propositional_subsumption,
% 4.02/0.96                [status(thm)],
% 4.02/0.96                [c_3086,c_16,c_949,c_2361]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3725,plain,
% 4.02/0.96      ( k7_setfam_1(sK1,sK2) = sK2
% 4.02/0.96      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
% 4.02/0.96      inference(renaming,[status(thm)],[c_3724]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_6,plain,
% 4.02/0.96      ( ~ r2_hidden(X0,k7_setfam_1(X1,X2))
% 4.02/0.96      | r2_hidden(k3_subset_1(X1,X0),X2)
% 4.02/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 4.02/0.96      | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 4.02/0.96      inference(cnf_transformation,[],[f52]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_552,plain,
% 4.02/0.96      ( r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
% 4.02/0.96      | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top
% 4.02/0.96      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.96      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 4.02/0.96      | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_622,plain,
% 4.02/0.96      ( r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
% 4.02/0.96      | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top
% 4.02/0.96      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 4.02/0.96      inference(forward_subsumption_resolution,
% 4.02/0.96                [status(thm)],
% 4.02/0.96                [c_552,c_550,c_548]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3129,plain,
% 4.02/0.96      ( r2_hidden(X0,sK2) != iProver_top
% 4.02/0.96      | r2_hidden(k3_subset_1(sK1,X0),k7_setfam_1(sK1,sK2)) = iProver_top
% 4.02/0.96      | m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_1145,c_622]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_17,plain,
% 4.02/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_695,plain,
% 4.02/0.96      ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 4.02/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 4.02/0.96      inference(instantiation,[status(thm)],[c_8]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_696,plain,
% 4.02/0.96      ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
% 4.02/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3729,plain,
% 4.02/0.96      ( r2_hidden(k3_subset_1(sK1,X0),k7_setfam_1(sK1,sK2)) = iProver_top
% 4.02/0.96      | r2_hidden(X0,sK2) != iProver_top ),
% 4.02/0.96      inference(global_propositional_subsumption,
% 4.02/0.96                [status(thm)],
% 4.02/0.96                [c_3129,c_17,c_696]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3730,plain,
% 4.02/0.96      ( r2_hidden(X0,sK2) != iProver_top
% 4.02/0.96      | r2_hidden(k3_subset_1(sK1,X0),k7_setfam_1(sK1,sK2)) = iProver_top ),
% 4.02/0.96      inference(renaming,[status(thm)],[c_3729]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_3739,plain,
% 4.02/0.96      ( k7_setfam_1(sK1,sK2) = sK2
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
% 4.02/0.96      | r2_hidden(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_3725,c_3730]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_4225,plain,
% 4.02/0.96      ( k7_setfam_1(sK1,sK2) = sK2
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
% 4.02/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_555,c_3739]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_5986,plain,
% 4.02/0.96      ( r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
% 4.02/0.96      | k7_setfam_1(sK1,sK2) = sK2 ),
% 4.02/0.96      inference(global_propositional_subsumption,[status(thm)],[c_4225,c_17]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_5987,plain,
% 4.02/0.96      ( k7_setfam_1(sK1,sK2) = sK2
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),k7_setfam_1(sK1,sK2)) = iProver_top
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top ),
% 4.02/0.96      inference(renaming,[status(thm)],[c_5986]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_9068,plain,
% 4.02/0.96      ( sK2 = k1_xboole_0
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
% 4.02/0.96      | r2_hidden(sK0(sK1,sK2,sK2),k1_xboole_0) = iProver_top ),
% 4.02/0.96      inference(demodulation,[status(thm)],[c_9046,c_5987]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_1,plain,
% 4.02/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.02/0.96      inference(cnf_transformation,[],[f35]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_557,plain,
% 4.02/0.96      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_10,plain,
% 4.02/0.96      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.02/0.96      inference(cnf_transformation,[],[f44]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_12,plain,
% 4.02/0.96      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 4.02/0.96      inference(cnf_transformation,[],[f46]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_181,plain,
% 4.02/0.96      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 4.02/0.96      inference(resolution,[status(thm)],[c_10,c_12]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_545,plain,
% 4.02/0.96      ( r2_hidden(X0,X1) != iProver_top
% 4.02/0.96      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.02/0.96      inference(predicate_to_equality,[status(thm)],[c_181]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_927,plain,
% 4.02/0.96      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.02/0.96      inference(superposition,[status(thm)],[c_557,c_545]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_9079,plain,
% 4.02/0.96      ( r2_hidden(X0,sK2) != iProver_top
% 4.02/0.96      | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
% 4.02/0.96      inference(demodulation,[status(thm)],[c_9046,c_3730]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_9667,plain,
% 4.02/0.96      ( r2_hidden(X0,sK2) != iProver_top ),
% 4.02/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_9079,c_927]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_10064,plain,
% 4.02/0.96      ( sK2 = k1_xboole_0 ),
% 4.02/0.96      inference(forward_subsumption_resolution,
% 4.02/0.96                [status(thm)],
% 4.02/0.96                [c_9068,c_927,c_9667]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_15,negated_conjecture,
% 4.02/0.96      ( k1_xboole_0 != sK2 ),
% 4.02/0.96      inference(cnf_transformation,[],[f49]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_10095,plain,
% 4.02/0.96      ( k1_xboole_0 != k1_xboole_0 ),
% 4.02/0.96      inference(demodulation,[status(thm)],[c_10064,c_15]) ).
% 4.02/0.96  
% 4.02/0.96  cnf(c_10096,plain,
% 4.02/0.96      ( $false ),
% 4.02/0.96      inference(equality_resolution_simp,[status(thm)],[c_10095]) ).
% 4.02/0.96  
% 4.02/0.96  
% 4.02/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.96  
% 4.02/0.96  ------                               Statistics
% 4.02/0.96  
% 4.02/0.96  ------ General
% 4.02/0.96  
% 4.02/0.96  abstr_ref_over_cycles:                  0
% 4.02/0.96  abstr_ref_under_cycles:                 0
% 4.02/0.96  gc_basic_clause_elim:                   0
% 4.02/0.96  forced_gc_time:                         0
% 4.02/0.96  parsing_time:                           0.008
% 4.02/0.96  unif_index_cands_time:                  0.
% 4.02/0.96  unif_index_add_time:                    0.
% 4.02/0.96  orderings_time:                         0.
% 4.02/0.96  out_proof_time:                         0.008
% 4.02/0.96  total_time:                             0.352
% 4.02/0.96  num_of_symbols:                         43
% 4.02/0.96  num_of_terms:                           9728
% 4.02/0.96  
% 4.02/0.96  ------ Preprocessing
% 4.02/0.96  
% 4.02/0.96  num_of_splits:                          0
% 4.02/0.96  num_of_split_atoms:                     0
% 4.02/0.96  num_of_reused_defs:                     0
% 4.02/0.96  num_eq_ax_congr_red:                    11
% 4.02/0.96  num_of_sem_filtered_clauses:            1
% 4.02/0.96  num_of_subtypes:                        0
% 4.02/0.96  monotx_restored_types:                  0
% 4.02/0.96  sat_num_of_epr_types:                   0
% 4.02/0.96  sat_num_of_non_cyclic_types:            0
% 4.02/0.96  sat_guarded_non_collapsed_types:        0
% 4.02/0.96  num_pure_diseq_elim:                    0
% 4.02/0.96  simp_replaced_by:                       0
% 4.02/0.96  res_preprocessed:                       84
% 4.02/0.96  prep_upred:                             0
% 4.02/0.96  prep_unflattend:                        0
% 4.02/0.96  smt_new_axioms:                         0
% 4.02/0.96  pred_elim_cands:                        2
% 4.02/0.96  pred_elim:                              1
% 4.02/0.96  pred_elim_cl:                           1
% 4.02/0.96  pred_elim_cycles:                       3
% 4.02/0.96  merged_defs:                            0
% 4.02/0.96  merged_defs_ncl:                        0
% 4.02/0.96  bin_hyper_res:                          0
% 4.02/0.96  prep_cycles:                            4
% 4.02/0.96  pred_elim_time:                         0.
% 4.02/0.96  splitting_time:                         0.
% 4.02/0.96  sem_filter_time:                        0.
% 4.02/0.96  monotx_time:                            0.001
% 4.02/0.96  subtype_inf_time:                       0.
% 4.02/0.96  
% 4.02/0.96  ------ Problem properties
% 4.02/0.96  
% 4.02/0.96  clauses:                                16
% 4.02/0.96  conjectures:                            3
% 4.02/0.96  epr:                                    1
% 4.02/0.96  horn:                                   13
% 4.02/0.96  ground:                                 3
% 4.02/0.96  unary:                                  4
% 4.02/0.96  binary:                                 5
% 4.02/0.96  lits:                                   44
% 4.02/0.96  lits_eq:                                9
% 4.02/0.96  fd_pure:                                0
% 4.02/0.96  fd_pseudo:                              0
% 4.02/0.96  fd_cond:                                1
% 4.02/0.96  fd_pseudo_cond:                         3
% 4.02/0.96  ac_symbols:                             0
% 4.02/0.96  
% 4.02/0.96  ------ Propositional Solver
% 4.02/0.96  
% 4.02/0.96  prop_solver_calls:                      27
% 4.02/0.96  prop_fast_solver_calls:                 766
% 4.02/0.96  smt_solver_calls:                       0
% 4.02/0.96  smt_fast_solver_calls:                  0
% 4.02/0.96  prop_num_of_clauses:                    3654
% 4.02/0.96  prop_preprocess_simplified:             7885
% 4.02/0.96  prop_fo_subsumed:                       12
% 4.02/0.96  prop_solver_time:                       0.
% 4.02/0.96  smt_solver_time:                        0.
% 4.02/0.96  smt_fast_solver_time:                   0.
% 4.02/0.96  prop_fast_solver_time:                  0.
% 4.02/0.96  prop_unsat_core_time:                   0.
% 4.02/0.96  
% 4.02/0.96  ------ QBF
% 4.02/0.96  
% 4.02/0.96  qbf_q_res:                              0
% 4.02/0.96  qbf_num_tautologies:                    0
% 4.02/0.96  qbf_prep_cycles:                        0
% 4.02/0.96  
% 4.02/0.96  ------ BMC1
% 4.02/0.96  
% 4.02/0.96  bmc1_current_bound:                     -1
% 4.02/0.96  bmc1_last_solved_bound:                 -1
% 4.02/0.96  bmc1_unsat_core_size:                   -1
% 4.02/0.96  bmc1_unsat_core_parents_size:           -1
% 4.02/0.96  bmc1_merge_next_fun:                    0
% 4.02/0.96  bmc1_unsat_core_clauses_time:           0.
% 4.02/0.96  
% 4.02/0.96  ------ Instantiation
% 4.02/0.96  
% 4.02/0.96  inst_num_of_clauses:                    1100
% 4.02/0.96  inst_num_in_passive:                    488
% 4.02/0.96  inst_num_in_active:                     476
% 4.02/0.96  inst_num_in_unprocessed:                136
% 4.02/0.96  inst_num_of_loops:                      530
% 4.02/0.96  inst_num_of_learning_restarts:          0
% 4.02/0.96  inst_num_moves_active_passive:          53
% 4.02/0.96  inst_lit_activity:                      0
% 4.02/0.96  inst_lit_activity_moves:                0
% 4.02/0.96  inst_num_tautologies:                   0
% 4.02/0.96  inst_num_prop_implied:                  0
% 4.02/0.96  inst_num_existing_simplified:           0
% 4.02/0.96  inst_num_eq_res_simplified:             0
% 4.02/0.96  inst_num_child_elim:                    0
% 4.02/0.96  inst_num_of_dismatching_blockings:      538
% 4.02/0.96  inst_num_of_non_proper_insts:           981
% 4.02/0.96  inst_num_of_duplicates:                 0
% 4.02/0.96  inst_inst_num_from_inst_to_res:         0
% 4.02/0.96  inst_dismatching_checking_time:         0.
% 4.02/0.96  
% 4.02/0.96  ------ Resolution
% 4.02/0.96  
% 4.02/0.96  res_num_of_clauses:                     0
% 4.02/0.96  res_num_in_passive:                     0
% 4.02/0.96  res_num_in_active:                      0
% 4.02/0.96  res_num_of_loops:                       88
% 4.02/0.96  res_forward_subset_subsumed:            87
% 4.02/0.96  res_backward_subset_subsumed:           0
% 4.02/0.96  res_forward_subsumed:                   0
% 4.02/0.96  res_backward_subsumed:                  0
% 4.02/0.96  res_forward_subsumption_resolution:     0
% 4.02/0.96  res_backward_subsumption_resolution:    0
% 4.02/0.96  res_clause_to_clause_subsumption:       1242
% 4.02/0.96  res_orphan_elimination:                 0
% 4.02/0.96  res_tautology_del:                      30
% 4.02/0.96  res_num_eq_res_simplified:              0
% 4.02/0.96  res_num_sel_changes:                    0
% 4.02/0.96  res_moves_from_active_to_pass:          0
% 4.02/0.96  
% 4.02/0.96  ------ Superposition
% 4.02/0.96  
% 4.02/0.96  sup_time_total:                         0.
% 4.02/0.96  sup_time_generating:                    0.
% 4.02/0.96  sup_time_sim_full:                      0.
% 4.02/0.96  sup_time_sim_immed:                     0.
% 4.02/0.96  
% 4.02/0.96  sup_num_of_clauses:                     192
% 4.02/0.96  sup_num_in_active:                      38
% 4.02/0.96  sup_num_in_passive:                     154
% 4.02/0.96  sup_num_of_loops:                       105
% 4.02/0.96  sup_fw_superposition:                   203
% 4.02/0.96  sup_bw_superposition:                   148
% 4.02/0.96  sup_immediate_simplified:               95
% 4.02/0.96  sup_given_eliminated:                   1
% 4.02/0.96  comparisons_done:                       0
% 4.02/0.96  comparisons_avoided:                    40
% 4.02/0.96  
% 4.02/0.96  ------ Simplifications
% 4.02/0.96  
% 4.02/0.96  
% 4.02/0.96  sim_fw_subset_subsumed:                 30
% 4.02/0.96  sim_bw_subset_subsumed:                 23
% 4.02/0.96  sim_fw_subsumed:                        56
% 4.02/0.96  sim_bw_subsumed:                        0
% 4.02/0.96  sim_fw_subsumption_res:                 7
% 4.02/0.96  sim_bw_subsumption_res:                 0
% 4.02/0.96  sim_tautology_del:                      14
% 4.02/0.96  sim_eq_tautology_del:                   7
% 4.02/0.96  sim_eq_res_simp:                        0
% 4.02/0.96  sim_fw_demodulated:                     2
% 4.02/0.96  sim_bw_demodulated:                     57
% 4.02/0.96  sim_light_normalised:                   9
% 4.02/0.96  sim_joinable_taut:                      0
% 4.02/0.96  sim_joinable_simp:                      0
% 4.02/0.96  sim_ac_normalised:                      0
% 4.02/0.96  sim_smt_subsumption:                    0
% 4.02/0.96  
%------------------------------------------------------------------------------
