%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:35 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 908 expanded)
%              Number of clauses        :   87 ( 153 expanded)
%              Number of leaves         :   31 ( 262 expanded)
%              Depth                    :   23
%              Number of atoms          :  564 (7214 expanded)
%              Number of equality atoms :  163 ( 939 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK4
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK4)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK4) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK3,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK3,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK2)
                      | ~ v3_pre_topc(X3,sK2) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK2)
                        & v3_pre_topc(X3,sK2) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( k1_xboole_0 = sK4
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK4)
            | ~ r2_hidden(sK3,X3)
            | ~ v4_pre_topc(X3,sK2)
            | ~ v3_pre_topc(X3,sK2) )
          & ( ( r2_hidden(sK3,X3)
              & v4_pre_topc(X3,sK2)
              & v3_pre_topc(X3,sK2) )
            | ~ r2_hidden(X3,sK4) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f56,f59,f58,f57])).

fof(f93,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f100,plain,(
    k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f60])).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(X0,sK4) = X0 ),
    inference(definition_unfolding,[],[f68,f100])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f101])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f102])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f103])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f104])).

fof(f106,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f82,f105])).

fof(f108,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = sK4 ),
    inference(definition_unfolding,[],[f66,f106,f100,f100])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f80,f100])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f107,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f65,f106])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f79,f107])).

fof(f16,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK4 = X0 ) ),
    inference(definition_unfolding,[],[f81,f100])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f89,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f109,plain,(
    ! [X0] : r1_tarski(sK4,X0) ),
    inference(definition_unfolding,[],[f67,f100])).

fof(f95,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f60])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f117,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f47])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_412,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_18,c_17])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_452,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_412,c_28])).

cnf(c_453,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1117,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1371,plain,
    ( m1_subset_1(sK3,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_1117])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(X0,sK4) = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = sK4 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1124,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1125,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2292,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4))) = k3_subset_1(X0,sK4) ),
    inference(superposition,[status(thm)],[c_1124,c_1125])).

cnf(c_3963,plain,
    ( k3_subset_1(X0,sK4) = k5_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_4,c_2292])).

cnf(c_13,negated_conjecture,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k3_subset_1(X1,X2))
    | sK4 = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1123,plain,
    ( sK4 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4330,plain,
    ( sK4 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X1,k5_xboole_0(X0,sK4)) = iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3963,c_1123])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12800,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | sK4 = X0
    | r2_hidden(X1,k5_xboole_0(X0,sK4)) = iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4330,c_51])).

cnf(c_12801,plain,
    ( sK4 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,k5_xboole_0(X0,sK4)) = iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_12800])).

cnf(c_12806,plain,
    ( sK4 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_12801])).

cnf(c_12837,plain,
    ( k2_struct_0(sK2) = sK4
    | r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_12806])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1127,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1122,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1747,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1122])).

cnf(c_22,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_20,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_437,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_438,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_63,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_440,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_29,c_28,c_63])).

cnf(c_459,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,X0)
    | k2_struct_0(sK2) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_440])).

cnf(c_460,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_21,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_60,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_462,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_29,c_28,c_60])).

cnf(c_1115,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
    | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_1259,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
    | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_1115])).

cnf(c_3606,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top
    | r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
    | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_1259])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_4817,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4820,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4817])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK4,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1130,plain,
    ( r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1118,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2293,plain,
    ( k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),k1_setfam_1(k6_enumset1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),sK4))) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
    inference(superposition,[status(thm)],[c_1118,c_1125])).

cnf(c_5442,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK4) = k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
    inference(superposition,[status(thm)],[c_4,c_2293])).

cnf(c_5645,plain,
    ( k3_subset_1(k1_zfmisc_1(k2_struct_0(sK2)),sK4) = k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
    inference(superposition,[status(thm)],[c_453,c_5442])).

cnf(c_5652,plain,
    ( k5_xboole_0(k1_zfmisc_1(k2_struct_0(sK2)),sK4) = k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
    inference(superposition,[status(thm)],[c_5645,c_3963])).

cnf(c_5832,plain,
    ( k5_xboole_0(k1_zfmisc_1(k2_struct_0(sK2)),sK4) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_6,c_5652])).

cnf(c_6123,plain,
    ( k1_zfmisc_1(k2_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_6,c_5832])).

cnf(c_6132,plain,
    ( r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6123,c_1127])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1126,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6718,plain,
    ( r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6132,c_1126])).

cnf(c_6730,plain,
    ( r1_tarski(sK4,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_6718])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1120,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6946,plain,
    ( r2_hidden(k2_struct_0(sK2),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6730,c_1120])).

cnf(c_12835,plain,
    ( u1_struct_0(sK2) = sK4
    | r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_12806])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_390,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_391,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_66,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_69,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_393,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_30,c_28,c_66,c_69])).

cnf(c_403,plain,
    ( r2_hidden(sK0(X0),X0)
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_393])).

cnf(c_404,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1215,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),sK0(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_654,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1396,plain,
    ( ~ r1_tarski(X0,sK0(u1_struct_0(sK2)))
    | r1_tarski(u1_struct_0(sK2),sK0(u1_struct_0(sK2)))
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_1708,plain,
    ( r1_tarski(u1_struct_0(sK2),sK0(u1_struct_0(sK2)))
    | ~ r1_tarski(sK4,sK0(u1_struct_0(sK2)))
    | u1_struct_0(sK2) != sK4 ),
    inference(instantiation,[status(thm)],[c_1396])).

cnf(c_1709,plain,
    ( r1_tarski(sK4,sK0(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13500,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12835,c_404,c_1215,c_1708,c_1709])).

cnf(c_13504,plain,
    ( r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_13500])).

cnf(c_13653,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12837,c_3606,c_4820,c_6946,c_13504])).

cnf(c_1617,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1120])).

cnf(c_13659,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_13653,c_1617])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.61/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.49  
% 7.61/1.49  ------  iProver source info
% 7.61/1.49  
% 7.61/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.49  git: non_committed_changes: false
% 7.61/1.49  git: last_make_outside_of_git: false
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  ------ Parsing...
% 7.61/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.49  ------ Proving...
% 7.61/1.49  ------ Problem Properties 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  clauses                                 21
% 7.61/1.49  conjectures                             8
% 7.61/1.49  EPR                                     5
% 7.61/1.49  Horn                                    19
% 7.61/1.49  unary                                   9
% 7.61/1.49  binary                                  5
% 7.61/1.49  lits                                    42
% 7.61/1.49  lits eq                                 8
% 7.61/1.49  fd_pure                                 0
% 7.61/1.49  fd_pseudo                               0
% 7.61/1.49  fd_cond                                 1
% 7.61/1.49  fd_pseudo_cond                          3
% 7.61/1.49  AC symbols                              0
% 7.61/1.49  
% 7.61/1.49  ------ Input Options Time Limit: Unbounded
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  Current options:
% 7.61/1.49  ------ 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ Proving...
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS status Theorem for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49   Resolution empty clause
% 7.61/1.49  
% 7.61/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  fof(f22,axiom,(
% 7.61/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f38,plain,(
% 7.61/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f22])).
% 7.61/1.49  
% 7.61/1.49  fof(f87,plain,(
% 7.61/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f38])).
% 7.61/1.49  
% 7.61/1.49  fof(f21,axiom,(
% 7.61/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f37,plain,(
% 7.61/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f21])).
% 7.61/1.49  
% 7.61/1.49  fof(f86,plain,(
% 7.61/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f37])).
% 7.61/1.49  
% 7.61/1.49  fof(f26,conjecture,(
% 7.61/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f27,negated_conjecture,(
% 7.61/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 7.61/1.49    inference(negated_conjecture,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  fof(f45,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f27])).
% 7.61/1.49  
% 7.61/1.49  fof(f46,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.61/1.49    inference(flattening,[],[f45])).
% 7.61/1.49  
% 7.61/1.49  fof(f55,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.61/1.49    inference(nnf_transformation,[],[f46])).
% 7.61/1.49  
% 7.61/1.49  fof(f56,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.61/1.49    inference(flattening,[],[f55])).
% 7.61/1.49  
% 7.61/1.49  fof(f59,plain,(
% 7.61/1.49    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f58,plain,(
% 7.61/1.49    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f57,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f60,plain,(
% 7.61/1.49    ((k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.61/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f56,f59,f58,f57])).
% 7.61/1.49  
% 7.61/1.49  fof(f93,plain,(
% 7.61/1.49    l1_pre_topc(sK2)),
% 7.61/1.49    inference(cnf_transformation,[],[f60])).
% 7.61/1.49  
% 7.61/1.49  fof(f94,plain,(
% 7.61/1.49    m1_subset_1(sK3,u1_struct_0(sK2))),
% 7.61/1.49    inference(cnf_transformation,[],[f60])).
% 7.61/1.49  
% 7.61/1.49  fof(f6,axiom,(
% 7.61/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f68,plain,(
% 7.61/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.61/1.49    inference(cnf_transformation,[],[f6])).
% 7.61/1.49  
% 7.61/1.49  fof(f100,plain,(
% 7.61/1.49    k1_xboole_0 = sK4),
% 7.61/1.49    inference(cnf_transformation,[],[f60])).
% 7.61/1.49  
% 7.61/1.49  fof(f110,plain,(
% 7.61/1.49    ( ! [X0] : (k5_xboole_0(X0,sK4) = X0) )),
% 7.61/1.49    inference(definition_unfolding,[],[f68,f100])).
% 7.61/1.49  
% 7.61/1.49  fof(f4,axiom,(
% 7.61/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f66,plain,(
% 7.61/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.61/1.49    inference(cnf_transformation,[],[f4])).
% 7.61/1.49  
% 7.61/1.49  fof(f17,axiom,(
% 7.61/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f82,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f17])).
% 7.61/1.49  
% 7.61/1.49  fof(f7,axiom,(
% 7.61/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f69,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f7])).
% 7.61/1.49  
% 7.61/1.49  fof(f8,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f70,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f8])).
% 7.61/1.49  
% 7.61/1.49  fof(f9,axiom,(
% 7.61/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f71,plain,(
% 7.61/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f9])).
% 7.61/1.49  
% 7.61/1.49  fof(f10,axiom,(
% 7.61/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f72,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f10])).
% 7.61/1.49  
% 7.61/1.49  fof(f11,axiom,(
% 7.61/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f73,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f11])).
% 7.61/1.49  
% 7.61/1.49  fof(f12,axiom,(
% 7.61/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f74,plain,(
% 7.61/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f12])).
% 7.61/1.49  
% 7.61/1.49  fof(f101,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f73,f74])).
% 7.61/1.49  
% 7.61/1.49  fof(f102,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f72,f101])).
% 7.61/1.49  
% 7.61/1.49  fof(f103,plain,(
% 7.61/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f71,f102])).
% 7.61/1.49  
% 7.61/1.49  fof(f104,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f70,f103])).
% 7.61/1.49  
% 7.61/1.49  fof(f105,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f69,f104])).
% 7.61/1.49  
% 7.61/1.49  fof(f106,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.61/1.49    inference(definition_unfolding,[],[f82,f105])).
% 7.61/1.49  
% 7.61/1.49  fof(f108,plain,(
% 7.61/1.49    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = sK4) )),
% 7.61/1.49    inference(definition_unfolding,[],[f66,f106,f100,f100])).
% 7.61/1.49  
% 7.61/1.49  fof(f15,axiom,(
% 7.61/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f80,plain,(
% 7.61/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f15])).
% 7.61/1.49  
% 7.61/1.49  fof(f112,plain,(
% 7.61/1.49    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(X0))) )),
% 7.61/1.49    inference(definition_unfolding,[],[f80,f100])).
% 7.61/1.49  
% 7.61/1.49  fof(f14,axiom,(
% 7.61/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f30,plain,(
% 7.61/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f14])).
% 7.61/1.49  
% 7.61/1.49  fof(f79,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f30])).
% 7.61/1.49  
% 7.61/1.49  fof(f3,axiom,(
% 7.61/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f65,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f3])).
% 7.61/1.49  
% 7.61/1.49  fof(f107,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.61/1.49    inference(definition_unfolding,[],[f65,f106])).
% 7.61/1.49  
% 7.61/1.49  fof(f111,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.61/1.49    inference(definition_unfolding,[],[f79,f107])).
% 7.61/1.49  
% 7.61/1.49  fof(f16,axiom,(
% 7.61/1.49    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f31,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 7.61/1.49    inference(ennf_transformation,[],[f16])).
% 7.61/1.49  
% 7.61/1.49  fof(f32,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 7.61/1.49    inference(flattening,[],[f31])).
% 7.61/1.49  
% 7.61/1.49  fof(f81,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 7.61/1.49    inference(cnf_transformation,[],[f32])).
% 7.61/1.49  
% 7.61/1.49  fof(f113,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK4 = X0) )),
% 7.61/1.49    inference(definition_unfolding,[],[f81,f100])).
% 7.61/1.49  
% 7.61/1.49  fof(f13,axiom,(
% 7.61/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f51,plain,(
% 7.61/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.61/1.49    inference(nnf_transformation,[],[f13])).
% 7.61/1.49  
% 7.61/1.49  fof(f52,plain,(
% 7.61/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.61/1.49    inference(rectify,[],[f51])).
% 7.61/1.49  
% 7.61/1.49  fof(f53,plain,(
% 7.61/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f54,plain,(
% 7.61/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.61/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 7.61/1.49  
% 7.61/1.49  fof(f76,plain,(
% 7.61/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.61/1.49    inference(cnf_transformation,[],[f54])).
% 7.61/1.49  
% 7.61/1.49  fof(f116,plain,(
% 7.61/1.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.61/1.49    inference(equality_resolution,[],[f76])).
% 7.61/1.49  
% 7.61/1.49  fof(f18,axiom,(
% 7.61/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f33,plain,(
% 7.61/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.61/1.49    inference(ennf_transformation,[],[f18])).
% 7.61/1.49  
% 7.61/1.49  fof(f83,plain,(
% 7.61/1.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f33])).
% 7.61/1.49  
% 7.61/1.49  fof(f99,plain,(
% 7.61/1.49    ( ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f60])).
% 7.61/1.49  
% 7.61/1.49  fof(f24,axiom,(
% 7.61/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f41,plain,(
% 7.61/1.49    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f24])).
% 7.61/1.49  
% 7.61/1.49  fof(f42,plain,(
% 7.61/1.49    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.61/1.49    inference(flattening,[],[f41])).
% 7.61/1.49  
% 7.61/1.49  fof(f89,plain,(
% 7.61/1.49    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f42])).
% 7.61/1.49  
% 7.61/1.49  fof(f92,plain,(
% 7.61/1.49    v2_pre_topc(sK2)),
% 7.61/1.49    inference(cnf_transformation,[],[f60])).
% 7.61/1.49  
% 7.61/1.49  fof(f25,axiom,(
% 7.61/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f43,plain,(
% 7.61/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f25])).
% 7.61/1.49  
% 7.61/1.49  fof(f44,plain,(
% 7.61/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.61/1.49    inference(flattening,[],[f43])).
% 7.61/1.49  
% 7.61/1.49  fof(f90,plain,(
% 7.61/1.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f44])).
% 7.61/1.49  
% 7.61/1.49  fof(f2,axiom,(
% 7.61/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f49,plain,(
% 7.61/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.61/1.49    inference(nnf_transformation,[],[f2])).
% 7.61/1.49  
% 7.61/1.49  fof(f50,plain,(
% 7.61/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.61/1.49    inference(flattening,[],[f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f62,plain,(
% 7.61/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.61/1.49    inference(cnf_transformation,[],[f50])).
% 7.61/1.49  
% 7.61/1.49  fof(f115,plain,(
% 7.61/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.61/1.49    inference(equality_resolution,[],[f62])).
% 7.61/1.49  
% 7.61/1.49  fof(f5,axiom,(
% 7.61/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f67,plain,(
% 7.61/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f5])).
% 7.61/1.49  
% 7.61/1.49  fof(f109,plain,(
% 7.61/1.49    ( ! [X0] : (r1_tarski(sK4,X0)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f67,f100])).
% 7.61/1.49  
% 7.61/1.49  fof(f95,plain,(
% 7.61/1.49    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 7.61/1.49    inference(cnf_transformation,[],[f60])).
% 7.61/1.49  
% 7.61/1.49  fof(f75,plain,(
% 7.61/1.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.61/1.49    inference(cnf_transformation,[],[f54])).
% 7.61/1.49  
% 7.61/1.49  fof(f117,plain,(
% 7.61/1.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.61/1.49    inference(equality_resolution,[],[f75])).
% 7.61/1.49  
% 7.61/1.49  fof(f20,axiom,(
% 7.61/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f36,plain,(
% 7.61/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.61/1.49    inference(ennf_transformation,[],[f20])).
% 7.61/1.49  
% 7.61/1.49  fof(f85,plain,(
% 7.61/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f36])).
% 7.61/1.49  
% 7.61/1.49  fof(f1,axiom,(
% 7.61/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f28,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 7.61/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.61/1.49  
% 7.61/1.49  fof(f29,plain,(
% 7.61/1.49    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f28])).
% 7.61/1.49  
% 7.61/1.49  fof(f47,plain,(
% 7.61/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f48,plain,(
% 7.61/1.49    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 7.61/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f47])).
% 7.61/1.49  
% 7.61/1.49  fof(f61,plain,(
% 7.61/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f48])).
% 7.61/1.49  
% 7.61/1.49  fof(f23,axiom,(
% 7.61/1.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.61/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f39,plain,(
% 7.61/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f23])).
% 7.61/1.49  
% 7.61/1.49  fof(f40,plain,(
% 7.61/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.61/1.49    inference(flattening,[],[f39])).
% 7.61/1.49  
% 7.61/1.49  fof(f88,plain,(
% 7.61/1.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f40])).
% 7.61/1.49  
% 7.61/1.49  fof(f91,plain,(
% 7.61/1.49    ~v2_struct_0(sK2)),
% 7.61/1.49    inference(cnf_transformation,[],[f60])).
% 7.61/1.49  
% 7.61/1.49  cnf(c_18,plain,
% 7.61/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_17,plain,
% 7.61/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_412,plain,
% 7.61/1.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.61/1.49      inference(resolution,[status(thm)],[c_18,c_17]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_28,negated_conjecture,
% 7.61/1.49      ( l1_pre_topc(sK2) ),
% 7.61/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_452,plain,
% 7.61/1.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 7.61/1.49      inference(resolution_lifted,[status(thm)],[c_412,c_28]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_453,plain,
% 7.61/1.49      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.61/1.49      inference(unflattening,[status(thm)],[c_452]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_27,negated_conjecture,
% 7.61/1.49      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1117,plain,
% 7.61/1.49      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1371,plain,
% 7.61/1.49      ( m1_subset_1(sK3,k2_struct_0(sK2)) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_453,c_1117]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_6,negated_conjecture,
% 7.61/1.49      ( k5_xboole_0(X0,sK4) = X0 ),
% 7.61/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4,negated_conjecture,
% 7.61/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = sK4 ),
% 7.61/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12,negated_conjecture,
% 7.61/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1124,plain,
% 7.61/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_11,plain,
% 7.61/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.61/1.49      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1125,plain,
% 7.61/1.49      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 7.61/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2292,plain,
% 7.61/1.49      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4))) = k3_subset_1(X0,sK4) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1124,c_1125]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_3963,plain,
% 7.61/1.49      ( k3_subset_1(X0,sK4) = k5_xboole_0(X0,sK4) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_4,c_2292]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13,negated_conjecture,
% 7.61/1.49      ( ~ m1_subset_1(X0,X1)
% 7.61/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.61/1.49      | r2_hidden(X0,X2)
% 7.61/1.49      | r2_hidden(X0,k3_subset_1(X1,X2))
% 7.61/1.49      | sK4 = X1 ),
% 7.61/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1123,plain,
% 7.61/1.49      ( sK4 = X0
% 7.61/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.61/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.61/1.49      | r2_hidden(X1,X2) = iProver_top
% 7.61/1.49      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4330,plain,
% 7.61/1.49      ( sK4 = X0
% 7.61/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.61/1.49      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 7.61/1.49      | r2_hidden(X1,k5_xboole_0(X0,sK4)) = iProver_top
% 7.61/1.49      | r2_hidden(X1,sK4) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_3963,c_1123]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_51,plain,
% 7.61/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12800,plain,
% 7.61/1.49      ( m1_subset_1(X1,X0) != iProver_top
% 7.61/1.49      | sK4 = X0
% 7.61/1.49      | r2_hidden(X1,k5_xboole_0(X0,sK4)) = iProver_top
% 7.61/1.49      | r2_hidden(X1,sK4) = iProver_top ),
% 7.61/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4330,c_51]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12801,plain,
% 7.61/1.49      ( sK4 = X0
% 7.61/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.61/1.49      | r2_hidden(X1,k5_xboole_0(X0,sK4)) = iProver_top
% 7.61/1.49      | r2_hidden(X1,sK4) = iProver_top ),
% 7.61/1.49      inference(renaming,[status(thm)],[c_12800]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12806,plain,
% 7.61/1.49      ( sK4 = X0
% 7.61/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.61/1.49      | r2_hidden(X1,X0) = iProver_top
% 7.61/1.49      | r2_hidden(X1,sK4) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_6,c_12801]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12837,plain,
% 7.61/1.49      ( k2_struct_0(sK2) = sK4
% 7.61/1.49      | r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top
% 7.61/1.49      | r2_hidden(sK3,sK4) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1371,c_12806]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_9,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1127,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.61/1.49      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_14,plain,
% 7.61/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.61/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1122,plain,
% 7.61/1.49      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1747,plain,
% 7.61/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.61/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1127,c_1122]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_22,negated_conjecture,
% 7.61/1.49      ( ~ v3_pre_topc(X0,sK2)
% 7.61/1.49      | ~ v4_pre_topc(X0,sK2)
% 7.61/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.61/1.49      | r2_hidden(X0,sK4)
% 7.61/1.49      | ~ r2_hidden(sK3,X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_20,plain,
% 7.61/1.49      ( v4_pre_topc(k2_struct_0(X0),X0)
% 7.61/1.49      | ~ v2_pre_topc(X0)
% 7.61/1.49      | ~ l1_pre_topc(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_29,negated_conjecture,
% 7.61/1.49      ( v2_pre_topc(sK2) ),
% 7.61/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_437,plain,
% 7.61/1.49      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK2 != X0 ),
% 7.61/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_438,plain,
% 7.61/1.49      ( v4_pre_topc(k2_struct_0(sK2),sK2) | ~ l1_pre_topc(sK2) ),
% 7.61/1.49      inference(unflattening,[status(thm)],[c_437]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_63,plain,
% 7.61/1.49      ( v4_pre_topc(k2_struct_0(sK2),sK2)
% 7.61/1.49      | ~ v2_pre_topc(sK2)
% 7.61/1.49      | ~ l1_pre_topc(sK2) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_440,plain,
% 7.61/1.49      ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_438,c_29,c_28,c_63]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_459,plain,
% 7.61/1.49      ( ~ v3_pre_topc(X0,sK2)
% 7.61/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.61/1.49      | r2_hidden(X0,sK4)
% 7.61/1.49      | ~ r2_hidden(sK3,X0)
% 7.61/1.49      | k2_struct_0(sK2) != X0
% 7.61/1.49      | sK2 != sK2 ),
% 7.61/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_440]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_460,plain,
% 7.61/1.49      ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
% 7.61/1.49      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.61/1.49      | r2_hidden(k2_struct_0(sK2),sK4)
% 7.61/1.49      | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
% 7.61/1.49      inference(unflattening,[status(thm)],[c_459]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_21,plain,
% 7.61/1.49      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.61/1.49      | ~ v2_pre_topc(X0)
% 7.61/1.49      | ~ l1_pre_topc(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_60,plain,
% 7.61/1.49      ( v3_pre_topc(k2_struct_0(sK2),sK2)
% 7.61/1.49      | ~ v2_pre_topc(sK2)
% 7.61/1.49      | ~ l1_pre_topc(sK2) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_462,plain,
% 7.61/1.49      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.61/1.49      | r2_hidden(k2_struct_0(sK2),sK4)
% 7.61/1.49      | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_460,c_29,c_28,c_60]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1115,plain,
% 7.61/1.49      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.61/1.49      | r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
% 7.61/1.49      | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1259,plain,
% 7.61/1.49      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 7.61/1.49      | r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
% 7.61/1.49      | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_453,c_1115]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_3606,plain,
% 7.61/1.49      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top
% 7.61/1.49      | r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
% 7.61/1.49      | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1747,c_1259]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f115]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4817,plain,
% 7.61/1.49      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4820,plain,
% 7.61/1.49      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_4817]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_5,negated_conjecture,
% 7.61/1.49      ( r1_tarski(sK4,X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f109]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1130,plain,
% 7.61/1.49      ( r1_tarski(sK4,X0) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_26,negated_conjecture,
% 7.61/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 7.61/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1118,plain,
% 7.61/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2293,plain,
% 7.61/1.49      ( k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),k1_setfam_1(k6_enumset1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)),sK4))) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1118,c_1125]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_5442,plain,
% 7.61/1.49      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK4) = k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_4,c_2293]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_5645,plain,
% 7.61/1.49      ( k3_subset_1(k1_zfmisc_1(k2_struct_0(sK2)),sK4) = k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_453,c_5442]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_5652,plain,
% 7.61/1.49      ( k5_xboole_0(k1_zfmisc_1(k2_struct_0(sK2)),sK4) = k5_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)),sK4) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_5645,c_3963]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_5832,plain,
% 7.61/1.49      ( k5_xboole_0(k1_zfmisc_1(k2_struct_0(sK2)),sK4) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_6,c_5652]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_6123,plain,
% 7.61/1.49      ( k1_zfmisc_1(k2_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_6,c_5832]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_6132,plain,
% 7.61/1.49      ( r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 7.61/1.49      | r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_6123,c_1127]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_10,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1126,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.61/1.49      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_6718,plain,
% 7.61/1.49      ( r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 7.61/1.49      | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_6132,c_1126]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_6730,plain,
% 7.61/1.49      ( r1_tarski(sK4,k2_struct_0(sK2)) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1130,c_6718]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_16,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1120,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_6946,plain,
% 7.61/1.49      ( r2_hidden(k2_struct_0(sK2),sK4) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_6730,c_1120]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12835,plain,
% 7.61/1.49      ( u1_struct_0(sK2) = sK4
% 7.61/1.49      | r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 7.61/1.49      | r2_hidden(sK3,sK4) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1117,c_12806]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_0,plain,
% 7.61/1.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_19,plain,
% 7.61/1.49      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_30,negated_conjecture,
% 7.61/1.49      ( ~ v2_struct_0(sK2) ),
% 7.61/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_390,plain,
% 7.61/1.49      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 7.61/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_391,plain,
% 7.61/1.49      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 7.61/1.49      inference(unflattening,[status(thm)],[c_390]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_66,plain,
% 7.61/1.49      ( v2_struct_0(sK2)
% 7.61/1.49      | ~ l1_struct_0(sK2)
% 7.61/1.49      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_69,plain,
% 7.61/1.49      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_393,plain,
% 7.61/1.49      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_391,c_30,c_28,c_66,c_69]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_403,plain,
% 7.61/1.49      ( r2_hidden(sK0(X0),X0) | u1_struct_0(sK2) != X0 ),
% 7.61/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_393]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_404,plain,
% 7.61/1.49      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 7.61/1.49      inference(unflattening,[status(thm)],[c_403]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1215,plain,
% 7.61/1.49      ( ~ r1_tarski(u1_struct_0(sK2),sK0(u1_struct_0(sK2)))
% 7.61/1.49      | ~ r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_654,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.61/1.49      theory(equality) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1396,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,sK0(u1_struct_0(sK2)))
% 7.61/1.49      | r1_tarski(u1_struct_0(sK2),sK0(u1_struct_0(sK2)))
% 7.61/1.49      | u1_struct_0(sK2) != X0 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_654]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1708,plain,
% 7.61/1.49      ( r1_tarski(u1_struct_0(sK2),sK0(u1_struct_0(sK2)))
% 7.61/1.49      | ~ r1_tarski(sK4,sK0(u1_struct_0(sK2)))
% 7.61/1.49      | u1_struct_0(sK2) != sK4 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_1396]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1709,plain,
% 7.61/1.49      ( r1_tarski(sK4,sK0(u1_struct_0(sK2))) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13500,plain,
% 7.61/1.49      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 7.61/1.49      | r2_hidden(sK3,sK4) = iProver_top ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_12835,c_404,c_1215,c_1708,c_1709]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13504,plain,
% 7.61/1.49      ( r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top
% 7.61/1.49      | r2_hidden(sK3,sK4) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_453,c_13500]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13653,plain,
% 7.61/1.49      ( r2_hidden(sK3,sK4) = iProver_top ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_12837,c_3606,c_4820,c_6946,c_13504]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1617,plain,
% 7.61/1.49      ( r2_hidden(X0,sK4) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1130,c_1120]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13659,plain,
% 7.61/1.49      ( $false ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_13653,c_1617]) ).
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  ------                               Statistics
% 7.61/1.49  
% 7.61/1.49  ------ Selected
% 7.61/1.49  
% 7.61/1.49  total_time:                             0.712
% 7.61/1.49  
%------------------------------------------------------------------------------
