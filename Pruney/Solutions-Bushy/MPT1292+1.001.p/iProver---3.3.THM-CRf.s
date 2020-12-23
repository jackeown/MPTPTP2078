%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1292+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:21 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 701 expanded)
%              Number of clauses        :   54 ( 199 expanded)
%              Number of leaves         :   13 ( 193 expanded)
%              Depth                    :   23
%              Number of atoms          :  275 (3146 expanded)
%              Number of equality atoms :   84 ( 712 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK2(X0,X5),X0)
        & r2_hidden(X5,sK2(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(X2,sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK0(X0,X1),X3) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK0(X0,X1),X4) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK0(X0,X1),X3) )
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( ( r2_hidden(sK1(X0,X1),X0)
              & r2_hidden(sK0(X0,X1),sK1(X0,X1)) )
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK2(X0,X5),X0)
                & r2_hidden(X5,sK2(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK5
        & m1_setfam_1(sK5,u1_struct_0(X0))
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK4))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
      & l1_struct_0(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k1_xboole_0 = sK5
    & m1_setfam_1(sK5,u1_struct_0(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    & l1_struct_0(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = X0
      | ~ m1_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    m1_setfam_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f34])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_732,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_289,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) != k1_zfmisc_1(k1_zfmisc_1(X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_290,plain,
    ( k5_setfam_1(X0,sK5) = k3_tarski(sK5)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) != k1_zfmisc_1(k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_766,plain,
    ( k5_setfam_1(X0,k1_xboole_0) = k3_tarski(k1_xboole_0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) != k1_zfmisc_1(k1_zfmisc_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_290,c_14])).

cnf(c_837,plain,
    ( k5_setfam_1(u1_struct_0(sK4),k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(equality_resolution,[status(thm)],[c_766])).

cnf(c_12,plain,
    ( ~ m1_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( m1_setfam_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = X1
    | u1_struct_0(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_263,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | k5_setfam_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_265,plain,
    ( k5_setfam_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_16])).

cnf(c_740,plain,
    ( k5_setfam_1(u1_struct_0(sK4),k1_xboole_0) = u1_struct_0(sK4) ),
    inference(light_normalisation,[status(thm)],[c_265,c_14])).

cnf(c_870,plain,
    ( u1_struct_0(sK4) = k3_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_837,c_740])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_298,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_299,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_723,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_761,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_723,c_14])).

cnf(c_975,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_xboole_0)))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_xboole_0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_870,c_761])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_730,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1257,plain,
    ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_xboole_0))))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_xboole_0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_730])).

cnf(c_7,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_230,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1398,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1257,c_231])).

cnf(c_1688,plain,
    ( k3_tarski(X0) = k1_xboole_0
    | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_1398])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK2(X1,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_729,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1403,plain,
    ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_1398])).

cnf(c_1409,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_1403])).

cnf(c_1498,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_1409])).

cnf(c_1504,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_1498])).

cnf(c_2145,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1688,c_1504])).

cnf(c_1582,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_1504])).

cnf(c_2146,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1688,c_1582])).

cnf(c_2150,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2145,c_2146])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_204,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_205,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_39,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_207,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_205,c_18,c_17,c_39])).

cnf(c_725,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_974,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_870,c_725])).

cnf(c_3805,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2150,c_974])).

cnf(c_41,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3805,c_41])).


%------------------------------------------------------------------------------
