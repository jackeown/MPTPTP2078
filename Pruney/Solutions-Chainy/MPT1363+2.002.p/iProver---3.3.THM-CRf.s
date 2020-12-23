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
% DateTime   : Thu Dec  3 12:17:56 EST 2020

% Result     : Theorem 31.70s
% Output     : CNFRefutation 31.70s
% Verified   : 
% Statistics : Number of formulae       :  262 (2174 expanded)
%              Number of clauses        :  168 ( 726 expanded)
%              Number of leaves         :   25 ( 569 expanded)
%              Depth                    :   23
%              Number of atoms          :  979 (11612 expanded)
%              Number of equality atoms :  431 (1209 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & v4_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & v2_compts_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK4,X0)
        & v4_pre_topc(sK4,X0)
        & r1_tarski(sK4,X1)
        & v2_compts_1(X1,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & v4_pre_topc(X2,X0)
            & r1_tarski(X2,sK3)
            & v2_compts_1(sK3,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(X2,X0)
                & v4_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & v2_compts_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,sK2)
              & v4_pre_topc(X2,sK2)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ~ v2_compts_1(sK4,sK2)
    & v4_pre_topc(sK4,sK2)
    & r1_tarski(sK4,sK3)
    & v2_compts_1(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f64,f63,f62])).

fof(f107,plain,(
    r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK1(X1,X2),X1)
        & sK1(X1,X2) = X2
        & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK1(X1,X2),X1)
                    & sK1(X1,X2) = X2
                    & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f106,plain,(
    v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                 => ( ( r1_tarski(X1,X2)
                      & X1 = X3 )
                   => k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3)
                  | ~ r1_tarski(X1,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3)
                  | ~ r1_tarski(X1,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3)
      | ~ r1_tarski(X1,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,(
    ! [X2,X0,X3] :
      ( k1_pre_topc(X0,X3) = k1_pre_topc(k1_pre_topc(X0,X2),X3)
      | ~ r1_tarski(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f102,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f105,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK1(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f109,plain,(
    ~ v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK1(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f108,plain,(
    v4_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3011,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3036,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4077,plain,
    ( k3_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_3011,c_3036])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3007,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_16,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_556,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_16,c_13])).

cnf(c_3003,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_4011,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3007,c_3003])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3008,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4261,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4011,c_3008])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3028,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4948,plain,
    ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_3028])).

cnf(c_45,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5190,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4948,c_45])).

cnf(c_5191,plain,
    ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5190])).

cnf(c_5199,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_4261,c_5191])).

cnf(c_21,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3026,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8429,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK2,sK3)),X0,k2_struct_0(k1_pre_topc(sK2,sK3))),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(sK3,X0,k2_struct_0(k1_pre_topc(sK2,sK3))),k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5199,c_3026])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_14,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_266,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_15])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_3006,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_5825,plain,
    ( k2_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_3006])).

cnf(c_6052,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | k2_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5825,c_45])).

cnf(c_6053,plain,
    ( k2_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6052])).

cnf(c_6061,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_4261,c_6053])).

cnf(c_8433,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(sK3,X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(sK3,X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8429,c_5199,c_6061])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3037,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_333,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_409,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_333])).

cnf(c_3004,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_4071,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3037,c_3004])).

cnf(c_8434,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8433,c_4071])).

cnf(c_109047,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_8434])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3428,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3788,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3428])).

cnf(c_3789,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3788])).

cnf(c_109477,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_109047,c_45,c_46,c_3789])).

cnf(c_109478,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_109477])).

cnf(c_109486,plain,
    ( v4_pre_topc(sK4,k1_pre_topc(sK2,sK3)) = iProver_top
    | v4_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4077,c_109478])).

cnf(c_109491,plain,
    ( v4_pre_topc(sK4,k1_pre_topc(sK2,sK3)) = iProver_top
    | v4_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_109486,c_4077])).

cnf(c_3034,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_30,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3017,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7390,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_3017])).

cnf(c_8016,plain,
    ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | v2_compts_1(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7390,c_45])).

cnf(c_8017,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8016])).

cnf(c_8022,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_8017])).

cnf(c_93065,plain,
    ( v2_compts_1(sK3,X0) = iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,u1_struct_0(X0)) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_8022])).

cnf(c_39,negated_conjecture,
    ( v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_48,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_557,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_3377,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3481,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3864,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3481])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4063,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4064,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4063])).

cnf(c_2144,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3240,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_3486,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3240])).

cnf(c_7351,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,u1_struct_0(X1))
    | u1_struct_0(X1) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3486])).

cnf(c_11980,plain,
    ( r1_tarski(sK3,u1_struct_0(X0))
    | ~ r1_tarski(sK3,k2_struct_0(X0))
    | u1_struct_0(X0) != k2_struct_0(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7351])).

cnf(c_11981,plain,
    ( u1_struct_0(X0) != k2_struct_0(X0)
    | sK3 != sK3
    | r1_tarski(sK3,u1_struct_0(X0)) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11980])).

cnf(c_93972,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,X0) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_93065,c_45,c_48,c_557,c_3377,c_3864,c_4064,c_11981])).

cnf(c_93973,plain,
    ( v2_compts_1(sK3,X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_93972])).

cnf(c_93982,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6061,c_93973])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_pre_topc(k1_pre_topc(X1,X0),X2) = k1_pre_topc(X1,X2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k1_pre_topc(k1_pre_topc(X1,X0),X2) = k1_pre_topc(X1,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_43])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | ~ l1_pre_topc(sK2)
    | k1_pre_topc(k1_pre_topc(sK2,X1),X0) = k1_pre_topc(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_653,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X1))))
    | k1_pre_topc(k1_pre_topc(sK2,X1),X0) = k1_pre_topc(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_42])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | k1_pre_topc(k1_pre_topc(sK2,X1),X0) = k1_pre_topc(sK2,X0) ),
    inference(renaming,[status(thm)],[c_653])).

cnf(c_3000,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_655,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3139,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3266,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0))))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3139])).

cnf(c_3267,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3266])).

cnf(c_3429,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3428])).

cnf(c_3477,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
    | k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3000,c_45,c_655,c_3267,c_3429])).

cnf(c_3478,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3477])).

cnf(c_4168,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK2,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_3478])).

cnf(c_4169,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK2,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4168,c_4011])).

cnf(c_5325,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,sK3),X0) = k1_pre_topc(sK2,X0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5199,c_4169])).

cnf(c_17093,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,sK3),X0) = k1_pre_topc(sK2,X0)
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5325,c_4261])).

cnf(c_17100,plain,
    ( k1_pre_topc(k1_pre_topc(sK2,sK3),sK4) = k1_pre_topc(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_3011,c_17093])).

cnf(c_3031,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5916,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK2,sK3),X0),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5199,c_3031])).

cnf(c_4209,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4063])).

cnf(c_4210,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4209])).

cnf(c_19959,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK2,sK3),X0),k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5916,c_45,c_46,c_3789,c_4210])).

cnf(c_19960,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK2,sK3),X0),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19959])).

cnf(c_19965,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17100,c_19960])).

cnf(c_49,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5913,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_3031])).

cnf(c_17197,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top
    | r1_tarski(sK4,u1_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17100,c_5913])).

cnf(c_17201,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top
    | r1_tarski(sK4,sK3) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17197,c_5199])).

cnf(c_20115,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19965,c_45,c_46,c_49,c_3789,c_4210,c_17201])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3009,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4260,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4011,c_3009])).

cnf(c_5198,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_4260,c_5191])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3035,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3039,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3035,c_6])).

cnf(c_3027,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6544,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3039,c_3027])).

cnf(c_35,plain,
    ( v2_compts_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3014,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_compts_1(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_15745,plain,
    ( v2_compts_1(u1_struct_0(X0),X1) = iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_compts_1(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6544,c_3014])).

cnf(c_39816,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK4)),X0) = iProver_top
    | v4_pre_topc(sK4,X0) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK4),X0) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5198,c_15745])).

cnf(c_39819,plain,
    ( v2_compts_1(sK4,X0) = iProver_top
    | v4_pre_topc(sK4,X0) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK4),X0) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39816,c_5198])).

cnf(c_40050,plain,
    ( v2_compts_1(sK4,k1_pre_topc(sK2,sK3)) = iProver_top
    | v4_pre_topc(sK4,k1_pre_topc(sK2,sK3)) != iProver_top
    | v1_compts_1(k1_pre_topc(sK2,sK3)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20115,c_39819])).

cnf(c_28,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3019,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,X2) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7717,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_3019])).

cnf(c_8398,plain,
    ( r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(X1,sK2) = iProver_top
    | sK1(X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7717,c_45])).

cnf(c_8399,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8398])).

cnf(c_8406,plain,
    ( sK1(X0,sK4) = sK4
    | v2_compts_1(sK4,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK4,k2_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4260,c_8399])).

cnf(c_36,negated_conjecture,
    ( ~ v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_51,plain,
    ( v2_compts_1(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9121,plain,
    ( sK1(X0,sK4) = sK4
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK4,k2_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8406,c_51])).

cnf(c_9129,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK4) = sK4
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6061,c_9121])).

cnf(c_13500,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9129,c_45,c_46,c_49,c_3789])).

cnf(c_27,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3020,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(sK1(X2,X0),X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7750,plain,
    ( v2_compts_1(X0,sK2) = iProver_top
    | v2_compts_1(sK1(X1,X0),X1) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_3020])).

cnf(c_7912,plain,
    ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | v2_compts_1(sK1(X1,X0),X1) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7750,c_45])).

cnf(c_7913,plain,
    ( v2_compts_1(X0,sK2) = iProver_top
    | v2_compts_1(sK1(X1,X0),X1) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7912])).

cnf(c_13503,plain,
    ( v2_compts_1(sK4,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK4,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(sK4,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13500,c_7913])).

cnf(c_13504,plain,
    ( v2_compts_1(sK4,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK4,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13503,c_6061])).

cnf(c_25,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3022,plain,
    ( v2_compts_1(k2_struct_0(X0),X0) != iProver_top
    | v1_compts_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6234,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v1_compts_1(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6061,c_3022])).

cnf(c_13239,plain,
    ( v1_compts_1(k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6234,c_45,c_46,c_3789,c_4210])).

cnf(c_13240,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v1_compts_1(k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_13239])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3033,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4157,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_3033])).

cnf(c_4161,plain,
    ( r1_tarski(sK4,k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4157,c_4011])).

cnf(c_3395,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3744,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_3395])).

cnf(c_3745,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3744])).

cnf(c_3378,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3377])).

cnf(c_3355,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ r1_tarski(sK4,k2_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3356,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | r1_tarski(sK4,k2_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3355])).

cnf(c_37,negated_conjecture,
    ( v4_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_50,plain,
    ( v4_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109491,c_93982,c_40050,c_13504,c_13240,c_4210,c_4161,c_3789,c_3745,c_3378,c_3356,c_51,c_50,c_49,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.70/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.70/4.49  
% 31.70/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.70/4.49  
% 31.70/4.49  ------  iProver source info
% 31.70/4.49  
% 31.70/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.70/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.70/4.49  git: non_committed_changes: false
% 31.70/4.49  git: last_make_outside_of_git: false
% 31.70/4.49  
% 31.70/4.49  ------ 
% 31.70/4.49  
% 31.70/4.49  ------ Input Options
% 31.70/4.49  
% 31.70/4.49  --out_options                           all
% 31.70/4.49  --tptp_safe_out                         true
% 31.70/4.49  --problem_path                          ""
% 31.70/4.49  --include_path                          ""
% 31.70/4.49  --clausifier                            res/vclausify_rel
% 31.70/4.49  --clausifier_options                    ""
% 31.70/4.49  --stdin                                 false
% 31.70/4.49  --stats_out                             all
% 31.70/4.49  
% 31.70/4.49  ------ General Options
% 31.70/4.49  
% 31.70/4.49  --fof                                   false
% 31.70/4.49  --time_out_real                         305.
% 31.70/4.49  --time_out_virtual                      -1.
% 31.70/4.49  --symbol_type_check                     false
% 31.70/4.49  --clausify_out                          false
% 31.70/4.49  --sig_cnt_out                           false
% 31.70/4.49  --trig_cnt_out                          false
% 31.70/4.49  --trig_cnt_out_tolerance                1.
% 31.70/4.49  --trig_cnt_out_sk_spl                   false
% 31.70/4.49  --abstr_cl_out                          false
% 31.70/4.49  
% 31.70/4.49  ------ Global Options
% 31.70/4.49  
% 31.70/4.49  --schedule                              default
% 31.70/4.49  --add_important_lit                     false
% 31.70/4.49  --prop_solver_per_cl                    1000
% 31.70/4.49  --min_unsat_core                        false
% 31.70/4.49  --soft_assumptions                      false
% 31.70/4.49  --soft_lemma_size                       3
% 31.70/4.49  --prop_impl_unit_size                   0
% 31.70/4.49  --prop_impl_unit                        []
% 31.70/4.49  --share_sel_clauses                     true
% 31.70/4.49  --reset_solvers                         false
% 31.70/4.49  --bc_imp_inh                            [conj_cone]
% 31.70/4.49  --conj_cone_tolerance                   3.
% 31.70/4.49  --extra_neg_conj                        none
% 31.70/4.49  --large_theory_mode                     true
% 31.70/4.49  --prolific_symb_bound                   200
% 31.70/4.49  --lt_threshold                          2000
% 31.70/4.49  --clause_weak_htbl                      true
% 31.70/4.49  --gc_record_bc_elim                     false
% 31.70/4.49  
% 31.70/4.49  ------ Preprocessing Options
% 31.70/4.49  
% 31.70/4.49  --preprocessing_flag                    true
% 31.70/4.49  --time_out_prep_mult                    0.1
% 31.70/4.49  --splitting_mode                        input
% 31.70/4.49  --splitting_grd                         true
% 31.70/4.49  --splitting_cvd                         false
% 31.70/4.49  --splitting_cvd_svl                     false
% 31.70/4.49  --splitting_nvd                         32
% 31.70/4.49  --sub_typing                            true
% 31.70/4.49  --prep_gs_sim                           true
% 31.70/4.49  --prep_unflatten                        true
% 31.70/4.49  --prep_res_sim                          true
% 31.70/4.49  --prep_upred                            true
% 31.70/4.49  --prep_sem_filter                       exhaustive
% 31.70/4.49  --prep_sem_filter_out                   false
% 31.70/4.49  --pred_elim                             true
% 31.70/4.49  --res_sim_input                         true
% 31.70/4.49  --eq_ax_congr_red                       true
% 31.70/4.49  --pure_diseq_elim                       true
% 31.70/4.49  --brand_transform                       false
% 31.70/4.49  --non_eq_to_eq                          false
% 31.70/4.49  --prep_def_merge                        true
% 31.70/4.49  --prep_def_merge_prop_impl              false
% 31.70/4.49  --prep_def_merge_mbd                    true
% 31.70/4.49  --prep_def_merge_tr_red                 false
% 31.70/4.49  --prep_def_merge_tr_cl                  false
% 31.70/4.49  --smt_preprocessing                     true
% 31.70/4.49  --smt_ac_axioms                         fast
% 31.70/4.49  --preprocessed_out                      false
% 31.70/4.49  --preprocessed_stats                    false
% 31.70/4.49  
% 31.70/4.49  ------ Abstraction refinement Options
% 31.70/4.49  
% 31.70/4.49  --abstr_ref                             []
% 31.70/4.49  --abstr_ref_prep                        false
% 31.70/4.49  --abstr_ref_until_sat                   false
% 31.70/4.49  --abstr_ref_sig_restrict                funpre
% 31.70/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.70/4.49  --abstr_ref_under                       []
% 31.70/4.49  
% 31.70/4.49  ------ SAT Options
% 31.70/4.49  
% 31.70/4.49  --sat_mode                              false
% 31.70/4.49  --sat_fm_restart_options                ""
% 31.70/4.49  --sat_gr_def                            false
% 31.70/4.49  --sat_epr_types                         true
% 31.70/4.49  --sat_non_cyclic_types                  false
% 31.70/4.49  --sat_finite_models                     false
% 31.70/4.49  --sat_fm_lemmas                         false
% 31.70/4.49  --sat_fm_prep                           false
% 31.70/4.49  --sat_fm_uc_incr                        true
% 31.70/4.49  --sat_out_model                         small
% 31.70/4.49  --sat_out_clauses                       false
% 31.70/4.49  
% 31.70/4.49  ------ QBF Options
% 31.70/4.49  
% 31.70/4.49  --qbf_mode                              false
% 31.70/4.49  --qbf_elim_univ                         false
% 31.70/4.49  --qbf_dom_inst                          none
% 31.70/4.49  --qbf_dom_pre_inst                      false
% 31.70/4.49  --qbf_sk_in                             false
% 31.70/4.49  --qbf_pred_elim                         true
% 31.70/4.49  --qbf_split                             512
% 31.70/4.49  
% 31.70/4.49  ------ BMC1 Options
% 31.70/4.49  
% 31.70/4.49  --bmc1_incremental                      false
% 31.70/4.49  --bmc1_axioms                           reachable_all
% 31.70/4.49  --bmc1_min_bound                        0
% 31.70/4.49  --bmc1_max_bound                        -1
% 31.70/4.49  --bmc1_max_bound_default                -1
% 31.70/4.49  --bmc1_symbol_reachability              true
% 31.70/4.49  --bmc1_property_lemmas                  false
% 31.70/4.49  --bmc1_k_induction                      false
% 31.70/4.49  --bmc1_non_equiv_states                 false
% 31.70/4.49  --bmc1_deadlock                         false
% 31.70/4.49  --bmc1_ucm                              false
% 31.70/4.49  --bmc1_add_unsat_core                   none
% 31.70/4.49  --bmc1_unsat_core_children              false
% 31.70/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.70/4.49  --bmc1_out_stat                         full
% 31.70/4.49  --bmc1_ground_init                      false
% 31.70/4.49  --bmc1_pre_inst_next_state              false
% 31.70/4.49  --bmc1_pre_inst_state                   false
% 31.70/4.49  --bmc1_pre_inst_reach_state             false
% 31.70/4.49  --bmc1_out_unsat_core                   false
% 31.70/4.49  --bmc1_aig_witness_out                  false
% 31.70/4.49  --bmc1_verbose                          false
% 31.70/4.49  --bmc1_dump_clauses_tptp                false
% 31.70/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.70/4.49  --bmc1_dump_file                        -
% 31.70/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.70/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.70/4.49  --bmc1_ucm_extend_mode                  1
% 31.70/4.49  --bmc1_ucm_init_mode                    2
% 31.70/4.49  --bmc1_ucm_cone_mode                    none
% 31.70/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.70/4.49  --bmc1_ucm_relax_model                  4
% 31.70/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.70/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.70/4.49  --bmc1_ucm_layered_model                none
% 31.70/4.49  --bmc1_ucm_max_lemma_size               10
% 31.70/4.49  
% 31.70/4.49  ------ AIG Options
% 31.70/4.49  
% 31.70/4.49  --aig_mode                              false
% 31.70/4.49  
% 31.70/4.49  ------ Instantiation Options
% 31.70/4.49  
% 31.70/4.49  --instantiation_flag                    true
% 31.70/4.49  --inst_sos_flag                         true
% 31.70/4.49  --inst_sos_phase                        true
% 31.70/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.70/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.70/4.49  --inst_lit_sel_side                     num_symb
% 31.70/4.49  --inst_solver_per_active                1400
% 31.70/4.49  --inst_solver_calls_frac                1.
% 31.70/4.49  --inst_passive_queue_type               priority_queues
% 31.70/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.70/4.49  --inst_passive_queues_freq              [25;2]
% 31.70/4.49  --inst_dismatching                      true
% 31.70/4.49  --inst_eager_unprocessed_to_passive     true
% 31.70/4.49  --inst_prop_sim_given                   true
% 31.70/4.49  --inst_prop_sim_new                     false
% 31.70/4.49  --inst_subs_new                         false
% 31.70/4.49  --inst_eq_res_simp                      false
% 31.70/4.49  --inst_subs_given                       false
% 31.70/4.49  --inst_orphan_elimination               true
% 31.70/4.49  --inst_learning_loop_flag               true
% 31.70/4.49  --inst_learning_start                   3000
% 31.70/4.49  --inst_learning_factor                  2
% 31.70/4.49  --inst_start_prop_sim_after_learn       3
% 31.70/4.49  --inst_sel_renew                        solver
% 31.70/4.49  --inst_lit_activity_flag                true
% 31.70/4.49  --inst_restr_to_given                   false
% 31.70/4.49  --inst_activity_threshold               500
% 31.70/4.49  --inst_out_proof                        true
% 31.70/4.49  
% 31.70/4.49  ------ Resolution Options
% 31.70/4.49  
% 31.70/4.49  --resolution_flag                       true
% 31.70/4.49  --res_lit_sel                           adaptive
% 31.70/4.49  --res_lit_sel_side                      none
% 31.70/4.49  --res_ordering                          kbo
% 31.70/4.49  --res_to_prop_solver                    active
% 31.70/4.49  --res_prop_simpl_new                    false
% 31.70/4.49  --res_prop_simpl_given                  true
% 31.70/4.49  --res_passive_queue_type                priority_queues
% 31.70/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.70/4.49  --res_passive_queues_freq               [15;5]
% 31.70/4.49  --res_forward_subs                      full
% 31.70/4.49  --res_backward_subs                     full
% 31.70/4.49  --res_forward_subs_resolution           true
% 31.70/4.49  --res_backward_subs_resolution          true
% 31.70/4.49  --res_orphan_elimination                true
% 31.70/4.49  --res_time_limit                        2.
% 31.70/4.49  --res_out_proof                         true
% 31.70/4.49  
% 31.70/4.49  ------ Superposition Options
% 31.70/4.49  
% 31.70/4.49  --superposition_flag                    true
% 31.70/4.49  --sup_passive_queue_type                priority_queues
% 31.70/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.70/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.70/4.49  --demod_completeness_check              fast
% 31.70/4.49  --demod_use_ground                      true
% 31.70/4.49  --sup_to_prop_solver                    passive
% 31.70/4.49  --sup_prop_simpl_new                    true
% 31.70/4.49  --sup_prop_simpl_given                  true
% 31.70/4.49  --sup_fun_splitting                     true
% 31.70/4.49  --sup_smt_interval                      50000
% 31.70/4.49  
% 31.70/4.49  ------ Superposition Simplification Setup
% 31.70/4.49  
% 31.70/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.70/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.70/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.70/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.70/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.70/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.70/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.70/4.49  --sup_immed_triv                        [TrivRules]
% 31.70/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.70/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.70/4.49  --sup_immed_bw_main                     []
% 31.70/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.70/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.70/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.70/4.49  --sup_input_bw                          []
% 31.70/4.49  
% 31.70/4.49  ------ Combination Options
% 31.70/4.49  
% 31.70/4.49  --comb_res_mult                         3
% 31.70/4.49  --comb_sup_mult                         2
% 31.70/4.49  --comb_inst_mult                        10
% 31.70/4.49  
% 31.70/4.49  ------ Debug Options
% 31.70/4.49  
% 31.70/4.49  --dbg_backtrace                         false
% 31.70/4.49  --dbg_dump_prop_clauses                 false
% 31.70/4.49  --dbg_dump_prop_clauses_file            -
% 31.70/4.49  --dbg_out_stat                          false
% 31.70/4.49  ------ Parsing...
% 31.70/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.70/4.49  
% 31.70/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.70/4.49  
% 31.70/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.70/4.49  
% 31.70/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.70/4.49  ------ Proving...
% 31.70/4.49  ------ Problem Properties 
% 31.70/4.49  
% 31.70/4.49  
% 31.70/4.49  clauses                                 41
% 31.70/4.49  conjectures                             7
% 31.70/4.49  EPR                                     8
% 31.70/4.49  Horn                                    37
% 31.70/4.49  unary                                   11
% 31.70/4.49  binary                                  6
% 31.70/4.49  lits                                    128
% 31.70/4.49  lits eq                                 15
% 31.70/4.49  fd_pure                                 0
% 31.70/4.49  fd_pseudo                               0
% 31.70/4.49  fd_cond                                 2
% 31.70/4.49  fd_pseudo_cond                          1
% 31.70/4.49  AC symbols                              0
% 31.70/4.49  
% 31.70/4.49  ------ Schedule dynamic 5 is on 
% 31.70/4.49  
% 31.70/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.70/4.49  
% 31.70/4.49  
% 31.70/4.49  ------ 
% 31.70/4.49  Current options:
% 31.70/4.49  ------ 
% 31.70/4.49  
% 31.70/4.49  ------ Input Options
% 31.70/4.49  
% 31.70/4.49  --out_options                           all
% 31.70/4.49  --tptp_safe_out                         true
% 31.70/4.49  --problem_path                          ""
% 31.70/4.49  --include_path                          ""
% 31.70/4.49  --clausifier                            res/vclausify_rel
% 31.70/4.49  --clausifier_options                    ""
% 31.70/4.49  --stdin                                 false
% 31.70/4.49  --stats_out                             all
% 31.70/4.49  
% 31.70/4.49  ------ General Options
% 31.70/4.49  
% 31.70/4.49  --fof                                   false
% 31.70/4.49  --time_out_real                         305.
% 31.70/4.49  --time_out_virtual                      -1.
% 31.70/4.49  --symbol_type_check                     false
% 31.70/4.49  --clausify_out                          false
% 31.70/4.49  --sig_cnt_out                           false
% 31.70/4.49  --trig_cnt_out                          false
% 31.70/4.49  --trig_cnt_out_tolerance                1.
% 31.70/4.49  --trig_cnt_out_sk_spl                   false
% 31.70/4.49  --abstr_cl_out                          false
% 31.70/4.49  
% 31.70/4.49  ------ Global Options
% 31.70/4.49  
% 31.70/4.49  --schedule                              default
% 31.70/4.49  --add_important_lit                     false
% 31.70/4.49  --prop_solver_per_cl                    1000
% 31.70/4.49  --min_unsat_core                        false
% 31.70/4.49  --soft_assumptions                      false
% 31.70/4.49  --soft_lemma_size                       3
% 31.70/4.49  --prop_impl_unit_size                   0
% 31.70/4.49  --prop_impl_unit                        []
% 31.70/4.49  --share_sel_clauses                     true
% 31.70/4.49  --reset_solvers                         false
% 31.70/4.49  --bc_imp_inh                            [conj_cone]
% 31.70/4.49  --conj_cone_tolerance                   3.
% 31.70/4.49  --extra_neg_conj                        none
% 31.70/4.49  --large_theory_mode                     true
% 31.70/4.49  --prolific_symb_bound                   200
% 31.70/4.49  --lt_threshold                          2000
% 31.70/4.49  --clause_weak_htbl                      true
% 31.70/4.49  --gc_record_bc_elim                     false
% 31.70/4.49  
% 31.70/4.49  ------ Preprocessing Options
% 31.70/4.49  
% 31.70/4.49  --preprocessing_flag                    true
% 31.70/4.49  --time_out_prep_mult                    0.1
% 31.70/4.49  --splitting_mode                        input
% 31.70/4.49  --splitting_grd                         true
% 31.70/4.49  --splitting_cvd                         false
% 31.70/4.49  --splitting_cvd_svl                     false
% 31.70/4.49  --splitting_nvd                         32
% 31.70/4.49  --sub_typing                            true
% 31.70/4.49  --prep_gs_sim                           true
% 31.70/4.49  --prep_unflatten                        true
% 31.70/4.49  --prep_res_sim                          true
% 31.70/4.49  --prep_upred                            true
% 31.70/4.49  --prep_sem_filter                       exhaustive
% 31.70/4.49  --prep_sem_filter_out                   false
% 31.70/4.49  --pred_elim                             true
% 31.70/4.49  --res_sim_input                         true
% 31.70/4.49  --eq_ax_congr_red                       true
% 31.70/4.49  --pure_diseq_elim                       true
% 31.70/4.49  --brand_transform                       false
% 31.70/4.49  --non_eq_to_eq                          false
% 31.70/4.49  --prep_def_merge                        true
% 31.70/4.49  --prep_def_merge_prop_impl              false
% 31.70/4.49  --prep_def_merge_mbd                    true
% 31.70/4.49  --prep_def_merge_tr_red                 false
% 31.70/4.49  --prep_def_merge_tr_cl                  false
% 31.70/4.49  --smt_preprocessing                     true
% 31.70/4.49  --smt_ac_axioms                         fast
% 31.70/4.49  --preprocessed_out                      false
% 31.70/4.49  --preprocessed_stats                    false
% 31.70/4.49  
% 31.70/4.49  ------ Abstraction refinement Options
% 31.70/4.49  
% 31.70/4.49  --abstr_ref                             []
% 31.70/4.49  --abstr_ref_prep                        false
% 31.70/4.49  --abstr_ref_until_sat                   false
% 31.70/4.49  --abstr_ref_sig_restrict                funpre
% 31.70/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.70/4.49  --abstr_ref_under                       []
% 31.70/4.49  
% 31.70/4.49  ------ SAT Options
% 31.70/4.49  
% 31.70/4.49  --sat_mode                              false
% 31.70/4.49  --sat_fm_restart_options                ""
% 31.70/4.49  --sat_gr_def                            false
% 31.70/4.49  --sat_epr_types                         true
% 31.70/4.49  --sat_non_cyclic_types                  false
% 31.70/4.49  --sat_finite_models                     false
% 31.70/4.49  --sat_fm_lemmas                         false
% 31.70/4.49  --sat_fm_prep                           false
% 31.70/4.49  --sat_fm_uc_incr                        true
% 31.70/4.49  --sat_out_model                         small
% 31.70/4.49  --sat_out_clauses                       false
% 31.70/4.49  
% 31.70/4.49  ------ QBF Options
% 31.70/4.49  
% 31.70/4.49  --qbf_mode                              false
% 31.70/4.49  --qbf_elim_univ                         false
% 31.70/4.49  --qbf_dom_inst                          none
% 31.70/4.49  --qbf_dom_pre_inst                      false
% 31.70/4.49  --qbf_sk_in                             false
% 31.70/4.49  --qbf_pred_elim                         true
% 31.70/4.49  --qbf_split                             512
% 31.70/4.49  
% 31.70/4.49  ------ BMC1 Options
% 31.70/4.49  
% 31.70/4.49  --bmc1_incremental                      false
% 31.70/4.49  --bmc1_axioms                           reachable_all
% 31.70/4.49  --bmc1_min_bound                        0
% 31.70/4.49  --bmc1_max_bound                        -1
% 31.70/4.49  --bmc1_max_bound_default                -1
% 31.70/4.49  --bmc1_symbol_reachability              true
% 31.70/4.49  --bmc1_property_lemmas                  false
% 31.70/4.49  --bmc1_k_induction                      false
% 31.70/4.49  --bmc1_non_equiv_states                 false
% 31.70/4.49  --bmc1_deadlock                         false
% 31.70/4.49  --bmc1_ucm                              false
% 31.70/4.49  --bmc1_add_unsat_core                   none
% 31.70/4.49  --bmc1_unsat_core_children              false
% 31.70/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.70/4.49  --bmc1_out_stat                         full
% 31.70/4.49  --bmc1_ground_init                      false
% 31.70/4.49  --bmc1_pre_inst_next_state              false
% 31.70/4.49  --bmc1_pre_inst_state                   false
% 31.70/4.49  --bmc1_pre_inst_reach_state             false
% 31.70/4.49  --bmc1_out_unsat_core                   false
% 31.70/4.49  --bmc1_aig_witness_out                  false
% 31.70/4.49  --bmc1_verbose                          false
% 31.70/4.49  --bmc1_dump_clauses_tptp                false
% 31.70/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.70/4.49  --bmc1_dump_file                        -
% 31.70/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.70/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.70/4.49  --bmc1_ucm_extend_mode                  1
% 31.70/4.49  --bmc1_ucm_init_mode                    2
% 31.70/4.49  --bmc1_ucm_cone_mode                    none
% 31.70/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.70/4.49  --bmc1_ucm_relax_model                  4
% 31.70/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.70/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.70/4.49  --bmc1_ucm_layered_model                none
% 31.70/4.49  --bmc1_ucm_max_lemma_size               10
% 31.70/4.49  
% 31.70/4.49  ------ AIG Options
% 31.70/4.49  
% 31.70/4.49  --aig_mode                              false
% 31.70/4.49  
% 31.70/4.49  ------ Instantiation Options
% 31.70/4.49  
% 31.70/4.49  --instantiation_flag                    true
% 31.70/4.49  --inst_sos_flag                         true
% 31.70/4.49  --inst_sos_phase                        true
% 31.70/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.70/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.70/4.49  --inst_lit_sel_side                     none
% 31.70/4.49  --inst_solver_per_active                1400
% 31.70/4.49  --inst_solver_calls_frac                1.
% 31.70/4.49  --inst_passive_queue_type               priority_queues
% 31.70/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.70/4.49  --inst_passive_queues_freq              [25;2]
% 31.70/4.49  --inst_dismatching                      true
% 31.70/4.49  --inst_eager_unprocessed_to_passive     true
% 31.70/4.49  --inst_prop_sim_given                   true
% 31.70/4.49  --inst_prop_sim_new                     false
% 31.70/4.49  --inst_subs_new                         false
% 31.70/4.49  --inst_eq_res_simp                      false
% 31.70/4.49  --inst_subs_given                       false
% 31.70/4.49  --inst_orphan_elimination               true
% 31.70/4.49  --inst_learning_loop_flag               true
% 31.70/4.49  --inst_learning_start                   3000
% 31.70/4.49  --inst_learning_factor                  2
% 31.70/4.49  --inst_start_prop_sim_after_learn       3
% 31.70/4.49  --inst_sel_renew                        solver
% 31.70/4.49  --inst_lit_activity_flag                true
% 31.70/4.49  --inst_restr_to_given                   false
% 31.70/4.49  --inst_activity_threshold               500
% 31.70/4.49  --inst_out_proof                        true
% 31.70/4.49  
% 31.70/4.49  ------ Resolution Options
% 31.70/4.49  
% 31.70/4.49  --resolution_flag                       false
% 31.70/4.49  --res_lit_sel                           adaptive
% 31.70/4.49  --res_lit_sel_side                      none
% 31.70/4.49  --res_ordering                          kbo
% 31.70/4.49  --res_to_prop_solver                    active
% 31.70/4.49  --res_prop_simpl_new                    false
% 31.70/4.49  --res_prop_simpl_given                  true
% 31.70/4.49  --res_passive_queue_type                priority_queues
% 31.70/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.70/4.49  --res_passive_queues_freq               [15;5]
% 31.70/4.49  --res_forward_subs                      full
% 31.70/4.49  --res_backward_subs                     full
% 31.70/4.49  --res_forward_subs_resolution           true
% 31.70/4.49  --res_backward_subs_resolution          true
% 31.70/4.49  --res_orphan_elimination                true
% 31.70/4.49  --res_time_limit                        2.
% 31.70/4.49  --res_out_proof                         true
% 31.70/4.49  
% 31.70/4.49  ------ Superposition Options
% 31.70/4.49  
% 31.70/4.49  --superposition_flag                    true
% 31.70/4.49  --sup_passive_queue_type                priority_queues
% 31.70/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.70/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.70/4.49  --demod_completeness_check              fast
% 31.70/4.49  --demod_use_ground                      true
% 31.70/4.49  --sup_to_prop_solver                    passive
% 31.70/4.49  --sup_prop_simpl_new                    true
% 31.70/4.49  --sup_prop_simpl_given                  true
% 31.70/4.49  --sup_fun_splitting                     true
% 31.70/4.49  --sup_smt_interval                      50000
% 31.70/4.49  
% 31.70/4.49  ------ Superposition Simplification Setup
% 31.70/4.49  
% 31.70/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.70/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.70/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.70/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.70/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.70/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.70/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.70/4.49  --sup_immed_triv                        [TrivRules]
% 31.70/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.70/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.70/4.49  --sup_immed_bw_main                     []
% 31.70/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.70/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.70/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.70/4.49  --sup_input_bw                          []
% 31.70/4.49  
% 31.70/4.49  ------ Combination Options
% 31.70/4.49  
% 31.70/4.49  --comb_res_mult                         3
% 31.70/4.49  --comb_sup_mult                         2
% 31.70/4.49  --comb_inst_mult                        10
% 31.70/4.49  
% 31.70/4.49  ------ Debug Options
% 31.70/4.49  
% 31.70/4.49  --dbg_backtrace                         false
% 31.70/4.49  --dbg_dump_prop_clauses                 false
% 31.70/4.49  --dbg_dump_prop_clauses_file            -
% 31.70/4.49  --dbg_out_stat                          false
% 31.70/4.49  
% 31.70/4.49  
% 31.70/4.49  
% 31.70/4.49  
% 31.70/4.49  ------ Proving...
% 31.70/4.49  
% 31.70/4.49  
% 31.70/4.49  % SZS status Theorem for theBenchmark.p
% 31.70/4.49  
% 31.70/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.70/4.49  
% 31.70/4.49  fof(f22,conjecture,(
% 31.70/4.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f23,negated_conjecture,(
% 31.70/4.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 31.70/4.49    inference(negated_conjecture,[],[f22])).
% 31.70/4.49  
% 31.70/4.49  fof(f46,plain,(
% 31.70/4.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 31.70/4.49    inference(ennf_transformation,[],[f23])).
% 31.70/4.49  
% 31.70/4.49  fof(f47,plain,(
% 31.70/4.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.70/4.49    inference(flattening,[],[f46])).
% 31.70/4.49  
% 31.70/4.49  fof(f64,plain,(
% 31.70/4.49    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK4,X0) & v4_pre_topc(sK4,X0) & r1_tarski(sK4,X1) & v2_compts_1(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.70/4.49    introduced(choice_axiom,[])).
% 31.70/4.49  
% 31.70/4.49  fof(f63,plain,(
% 31.70/4.49    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,sK3) & v2_compts_1(sK3,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.70/4.49    introduced(choice_axiom,[])).
% 31.70/4.49  
% 31.70/4.49  fof(f62,plain,(
% 31.70/4.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(X2,sK2) & v4_pre_topc(X2,sK2) & r1_tarski(X2,X1) & v2_compts_1(X1,sK2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 31.70/4.49    introduced(choice_axiom,[])).
% 31.70/4.49  
% 31.70/4.49  fof(f65,plain,(
% 31.70/4.49    ((~v2_compts_1(sK4,sK2) & v4_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & v2_compts_1(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 31.70/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f64,f63,f62])).
% 31.70/4.49  
% 31.70/4.49  fof(f107,plain,(
% 31.70/4.49    r1_tarski(sK4,sK3)),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  fof(f3,axiom,(
% 31.70/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f24,plain,(
% 31.70/4.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.70/4.49    inference(ennf_transformation,[],[f3])).
% 31.70/4.49  
% 31.70/4.49  fof(f70,plain,(
% 31.70/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f24])).
% 31.70/4.49  
% 31.70/4.49  fof(f103,plain,(
% 31.70/4.49    l1_pre_topc(sK2)),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  fof(f12,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f32,plain,(
% 31.70/4.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f12])).
% 31.70/4.49  
% 31.70/4.49  fof(f82,plain,(
% 31.70/4.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f32])).
% 31.70/4.49  
% 31.70/4.49  fof(f10,axiom,(
% 31.70/4.49    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f29,plain,(
% 31.70/4.49    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f10])).
% 31.70/4.49  
% 31.70/4.49  fof(f79,plain,(
% 31.70/4.49    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f29])).
% 31.70/4.49  
% 31.70/4.49  fof(f104,plain,(
% 31.70/4.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  fof(f15,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f36,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f15])).
% 31.70/4.49  
% 31.70/4.49  fof(f85,plain,(
% 31.70/4.49    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f36])).
% 31.70/4.49  
% 31.70/4.49  fof(f17,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f38,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f17])).
% 31.70/4.49  
% 31.70/4.49  fof(f52,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(nnf_transformation,[],[f38])).
% 31.70/4.49  
% 31.70/4.49  fof(f53,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(rectify,[],[f52])).
% 31.70/4.49  
% 31.70/4.49  fof(f54,plain,(
% 31.70/4.49    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 31.70/4.49    introduced(choice_axiom,[])).
% 31.70/4.49  
% 31.70/4.49  fof(f55,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).
% 31.70/4.49  
% 31.70/4.49  fof(f90,plain,(
% 31.70/4.49    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f55])).
% 31.70/4.49  
% 31.70/4.49  fof(f115,plain,(
% 31.70/4.49    ( ! [X0,X3,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(equality_resolution,[],[f90])).
% 31.70/4.49  
% 31.70/4.49  fof(f9,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f27,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f9])).
% 31.70/4.49  
% 31.70/4.49  fof(f28,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(flattening,[],[f27])).
% 31.70/4.49  
% 31.70/4.49  fof(f51,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(nnf_transformation,[],[f28])).
% 31.70/4.49  
% 31.70/4.49  fof(f77,plain,(
% 31.70/4.49    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f51])).
% 31.70/4.49  
% 31.70/4.49  fof(f113,plain,(
% 31.70/4.49    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(equality_resolution,[],[f77])).
% 31.70/4.49  
% 31.70/4.49  fof(f11,axiom,(
% 31.70/4.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f30,plain,(
% 31.70/4.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.70/4.49    inference(ennf_transformation,[],[f11])).
% 31.70/4.49  
% 31.70/4.49  fof(f31,plain,(
% 31.70/4.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(flattening,[],[f30])).
% 31.70/4.49  
% 31.70/4.49  fof(f81,plain,(
% 31.70/4.49    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f31])).
% 31.70/4.49  
% 31.70/4.49  fof(f80,plain,(
% 31.70/4.49    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f31])).
% 31.70/4.49  
% 31.70/4.49  fof(f2,axiom,(
% 31.70/4.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f48,plain,(
% 31.70/4.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.70/4.49    inference(nnf_transformation,[],[f2])).
% 31.70/4.49  
% 31.70/4.49  fof(f49,plain,(
% 31.70/4.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.70/4.49    inference(flattening,[],[f48])).
% 31.70/4.49  
% 31.70/4.49  fof(f67,plain,(
% 31.70/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.70/4.49    inference(cnf_transformation,[],[f49])).
% 31.70/4.49  
% 31.70/4.49  fof(f111,plain,(
% 31.70/4.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.70/4.49    inference(equality_resolution,[],[f67])).
% 31.70/4.49  
% 31.70/4.49  fof(f7,axiom,(
% 31.70/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f26,plain,(
% 31.70/4.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 31.70/4.49    inference(ennf_transformation,[],[f7])).
% 31.70/4.49  
% 31.70/4.49  fof(f74,plain,(
% 31.70/4.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 31.70/4.49    inference(cnf_transformation,[],[f26])).
% 31.70/4.49  
% 31.70/4.49  fof(f8,axiom,(
% 31.70/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f50,plain,(
% 31.70/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.70/4.49    inference(nnf_transformation,[],[f8])).
% 31.70/4.49  
% 31.70/4.49  fof(f76,plain,(
% 31.70/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f50])).
% 31.70/4.49  
% 31.70/4.49  fof(f19,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f40,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f19])).
% 31.70/4.49  
% 31.70/4.49  fof(f41,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(flattening,[],[f40])).
% 31.70/4.49  
% 31.70/4.49  fof(f57,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(nnf_transformation,[],[f41])).
% 31.70/4.49  
% 31.70/4.49  fof(f58,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(rectify,[],[f57])).
% 31.70/4.49  
% 31.70/4.49  fof(f59,plain,(
% 31.70/4.49    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 31.70/4.49    introduced(choice_axiom,[])).
% 31.70/4.49  
% 31.70/4.49  fof(f60,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).
% 31.70/4.49  
% 31.70/4.49  fof(f93,plain,(
% 31.70/4.49    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f60])).
% 31.70/4.49  
% 31.70/4.49  fof(f116,plain,(
% 31.70/4.49    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(equality_resolution,[],[f93])).
% 31.70/4.49  
% 31.70/4.49  fof(f106,plain,(
% 31.70/4.49    v2_compts_1(sK3,sK2)),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  fof(f69,plain,(
% 31.70/4.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f49])).
% 31.70/4.49  
% 31.70/4.49  fof(f13,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f33,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f13])).
% 31.70/4.49  
% 31.70/4.49  fof(f83,plain,(
% 31.70/4.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f33])).
% 31.70/4.49  
% 31.70/4.49  fof(f14,axiom,(
% 31.70/4.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) => ((r1_tarski(X1,X2) & X1 = X3) => k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3))))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f34,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) | (~r1_tarski(X1,X2) | X1 != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.70/4.49    inference(ennf_transformation,[],[f14])).
% 31.70/4.49  
% 31.70/4.49  fof(f35,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) | ~r1_tarski(X1,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.70/4.49    inference(flattening,[],[f34])).
% 31.70/4.49  
% 31.70/4.49  fof(f84,plain,(
% 31.70/4.49    ( ! [X2,X0,X3,X1] : (k1_pre_topc(X0,X1) = k1_pre_topc(k1_pre_topc(X0,X2),X3) | ~r1_tarski(X1,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f35])).
% 31.70/4.49  
% 31.70/4.49  fof(f114,plain,(
% 31.70/4.49    ( ! [X2,X0,X3] : (k1_pre_topc(X0,X3) = k1_pre_topc(k1_pre_topc(X0,X2),X3) | ~r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.70/4.49    inference(equality_resolution,[],[f84])).
% 31.70/4.49  
% 31.70/4.49  fof(f102,plain,(
% 31.70/4.49    v2_pre_topc(sK2)),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  fof(f16,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f37,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f16])).
% 31.70/4.49  
% 31.70/4.49  fof(f86,plain,(
% 31.70/4.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f37])).
% 31.70/4.49  
% 31.70/4.49  fof(f105,plain,(
% 31.70/4.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  fof(f6,axiom,(
% 31.70/4.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f73,plain,(
% 31.70/4.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 31.70/4.49    inference(cnf_transformation,[],[f6])).
% 31.70/4.49  
% 31.70/4.49  fof(f5,axiom,(
% 31.70/4.49    ! [X0] : k2_subset_1(X0) = X0),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f72,plain,(
% 31.70/4.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 31.70/4.49    inference(cnf_transformation,[],[f5])).
% 31.70/4.49  
% 31.70/4.49  fof(f21,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f44,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f21])).
% 31.70/4.49  
% 31.70/4.49  fof(f45,plain,(
% 31.70/4.49    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(flattening,[],[f44])).
% 31.70/4.49  
% 31.70/4.49  fof(f101,plain,(
% 31.70/4.49    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f45])).
% 31.70/4.49  
% 31.70/4.49  fof(f95,plain,(
% 31.70/4.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK1(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f60])).
% 31.70/4.49  
% 31.70/4.49  fof(f109,plain,(
% 31.70/4.49    ~v2_compts_1(sK4,sK2)),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  fof(f96,plain,(
% 31.70/4.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK1(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f60])).
% 31.70/4.49  
% 31.70/4.49  fof(f18,axiom,(
% 31.70/4.49    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 31.70/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.49  
% 31.70/4.49  fof(f39,plain,(
% 31.70/4.49    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(ennf_transformation,[],[f18])).
% 31.70/4.49  
% 31.70/4.49  fof(f56,plain,(
% 31.70/4.49    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 31.70/4.49    inference(nnf_transformation,[],[f39])).
% 31.70/4.49  
% 31.70/4.49  fof(f92,plain,(
% 31.70/4.49    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 31.70/4.49    inference(cnf_transformation,[],[f56])).
% 31.70/4.49  
% 31.70/4.49  fof(f75,plain,(
% 31.70/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.70/4.49    inference(cnf_transformation,[],[f50])).
% 31.70/4.49  
% 31.70/4.49  fof(f108,plain,(
% 31.70/4.49    v4_pre_topc(sK4,sK2)),
% 31.70/4.49    inference(cnf_transformation,[],[f65])).
% 31.70/4.49  
% 31.70/4.49  cnf(c_38,negated_conjecture,
% 31.70/4.49      ( r1_tarski(sK4,sK3) ),
% 31.70/4.49      inference(cnf_transformation,[],[f107]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3011,plain,
% 31.70/4.49      ( r1_tarski(sK4,sK3) = iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_4,plain,
% 31.70/4.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 31.70/4.49      inference(cnf_transformation,[],[f70]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3036,plain,
% 31.70/4.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_4077,plain,
% 31.70/4.49      ( k3_xboole_0(sK4,sK3) = sK4 ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_3011,c_3036]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_42,negated_conjecture,
% 31.70/4.49      ( l1_pre_topc(sK2) ),
% 31.70/4.49      inference(cnf_transformation,[],[f103]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3007,plain,
% 31.70/4.49      ( l1_pre_topc(sK2) = iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_16,plain,
% 31.70/4.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 31.70/4.49      inference(cnf_transformation,[],[f82]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_13,plain,
% 31.70/4.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 31.70/4.49      inference(cnf_transformation,[],[f79]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_556,plain,
% 31.70/4.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 31.70/4.49      inference(resolution,[status(thm)],[c_16,c_13]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3003,plain,
% 31.70/4.49      ( u1_struct_0(X0) = k2_struct_0(X0)
% 31.70/4.49      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_4011,plain,
% 31.70/4.49      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_3007,c_3003]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_41,negated_conjecture,
% 31.70/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 31.70/4.49      inference(cnf_transformation,[],[f104]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3008,plain,
% 31.70/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_4261,plain,
% 31.70/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 31.70/4.49      inference(demodulation,[status(thm)],[c_4011,c_3008]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_19,plain,
% 31.70/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.49      | ~ l1_pre_topc(X1)
% 31.70/4.49      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 31.70/4.49      inference(cnf_transformation,[],[f85]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3028,plain,
% 31.70/4.49      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 31.70/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.49      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_4948,plain,
% 31.70/4.49      ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_4011,c_3028]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_45,plain,
% 31.70/4.49      ( l1_pre_topc(sK2) = iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_5190,plain,
% 31.70/4.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
% 31.70/4.49      inference(global_propositional_subsumption,
% 31.70/4.49                [status(thm)],
% 31.70/4.49                [c_4948,c_45]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_5191,plain,
% 31.70/4.49      ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 31.70/4.49      inference(renaming,[status(thm)],[c_5190]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_5199,plain,
% 31.70/4.49      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_4261,c_5191]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_21,plain,
% 31.70/4.49      ( ~ v4_pre_topc(X0,X1)
% 31.70/4.49      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 31.70/4.49      | ~ m1_pre_topc(X2,X1)
% 31.70/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.49      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 31.70/4.49      | ~ l1_pre_topc(X1) ),
% 31.70/4.49      inference(cnf_transformation,[],[f115]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3026,plain,
% 31.70/4.49      ( v4_pre_topc(X0,X1) != iProver_top
% 31.70/4.49      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
% 31.70/4.49      | m1_pre_topc(X2,X1) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.49      | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 31.70/4.49      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_8429,plain,
% 31.70/4.49      ( v4_pre_topc(X0,X1) != iProver_top
% 31.70/4.49      | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK2,sK3)),X0,k2_struct_0(k1_pre_topc(sK2,sK3))),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.49      | m1_subset_1(k9_subset_1(sK3,X0,k2_struct_0(k1_pre_topc(sK2,sK3))),k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.49      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_5199,c_3026]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_12,plain,
% 31.70/4.49      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 31.70/4.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 31.70/4.49      | ~ l1_pre_topc(X0)
% 31.70/4.49      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 31.70/4.49      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 31.70/4.49      inference(cnf_transformation,[],[f113]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_14,plain,
% 31.70/4.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 31.70/4.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 31.70/4.49      | ~ l1_pre_topc(X0) ),
% 31.70/4.49      inference(cnf_transformation,[],[f81]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_260,plain,
% 31.70/4.49      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 31.70/4.49      | ~ l1_pre_topc(X0)
% 31.70/4.49      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 31.70/4.49      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 31.70/4.49      inference(global_propositional_subsumption,
% 31.70/4.49                [status(thm)],
% 31.70/4.49                [c_12,c_14]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_261,plain,
% 31.70/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.49      | ~ l1_pre_topc(X1)
% 31.70/4.49      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 31.70/4.49      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 31.70/4.49      inference(renaming,[status(thm)],[c_260]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_15,plain,
% 31.70/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.49      | ~ l1_pre_topc(X1)
% 31.70/4.49      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 31.70/4.49      inference(cnf_transformation,[],[f80]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_266,plain,
% 31.70/4.49      ( ~ l1_pre_topc(X1)
% 31.70/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.49      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 31.70/4.49      inference(global_propositional_subsumption,
% 31.70/4.49                [status(thm)],
% 31.70/4.49                [c_261,c_15]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_267,plain,
% 31.70/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.49      | ~ l1_pre_topc(X1)
% 31.70/4.49      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 31.70/4.49      inference(renaming,[status(thm)],[c_266]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3006,plain,
% 31.70/4.49      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 31.70/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.49      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_5825,plain,
% 31.70/4.49      ( k2_struct_0(k1_pre_topc(sK2,X0)) = X0
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_4011,c_3006]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_6052,plain,
% 31.70/4.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | k2_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
% 31.70/4.49      inference(global_propositional_subsumption,
% 31.70/4.49                [status(thm)],
% 31.70/4.49                [c_5825,c_45]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_6053,plain,
% 31.70/4.49      ( k2_struct_0(k1_pre_topc(sK2,X0)) = X0
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 31.70/4.49      inference(renaming,[status(thm)],[c_6052]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_6061,plain,
% 31.70/4.49      ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_4261,c_6053]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_8433,plain,
% 31.70/4.49      ( v4_pre_topc(X0,X1) != iProver_top
% 31.70/4.49      | v4_pre_topc(k9_subset_1(sK3,X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.49      | m1_subset_1(k9_subset_1(sK3,X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.49      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.49      inference(light_normalisation,[status(thm)],[c_8429,c_5199,c_6061]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3,plain,
% 31.70/4.49      ( r1_tarski(X0,X0) ),
% 31.70/4.49      inference(cnf_transformation,[],[f111]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3037,plain,
% 31.70/4.49      ( r1_tarski(X0,X0) = iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_8,plain,
% 31.70/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.70/4.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 31.70/4.49      inference(cnf_transformation,[],[f74]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_9,plain,
% 31.70/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.70/4.49      inference(cnf_transformation,[],[f76]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_332,plain,
% 31.70/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.70/4.49      inference(prop_impl,[status(thm)],[c_9]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_333,plain,
% 31.70/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.70/4.49      inference(renaming,[status(thm)],[c_332]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_409,plain,
% 31.70/4.49      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 31.70/4.49      inference(bin_hyper_res,[status(thm)],[c_8,c_333]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3004,plain,
% 31.70/4.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 31.70/4.49      | r1_tarski(X2,X0) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_4071,plain,
% 31.70/4.49      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_3037,c_3004]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_8434,plain,
% 31.70/4.49      ( v4_pre_topc(X0,X1) != iProver_top
% 31.70/4.49      | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.49      | m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.49      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.49      inference(demodulation,[status(thm)],[c_8433,c_4071]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_109047,plain,
% 31.70/4.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 31.70/4.49      | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.49      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_4011,c_8434]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_46,plain,
% 31.70/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3428,plain,
% 31.70/4.49      ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
% 31.70/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.49      | ~ l1_pre_topc(sK2) ),
% 31.70/4.49      inference(instantiation,[status(thm)],[c_14]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3788,plain,
% 31.70/4.49      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
% 31.70/4.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.49      | ~ l1_pre_topc(sK2) ),
% 31.70/4.49      inference(instantiation,[status(thm)],[c_3428]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3789,plain,
% 31.70/4.49      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
% 31.70/4.49      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.49      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_3788]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_109477,plain,
% 31.70/4.49      ( m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | v4_pre_topc(X0,sK2) != iProver_top
% 31.70/4.49      | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top ),
% 31.70/4.49      inference(global_propositional_subsumption,
% 31.70/4.49                [status(thm)],
% 31.70/4.49                [c_109047,c_45,c_46,c_3789]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_109478,plain,
% 31.70/4.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 31.70/4.49      | v4_pre_topc(k3_xboole_0(X0,sK3),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(sK3)) != iProver_top ),
% 31.70/4.49      inference(renaming,[status(thm)],[c_109477]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_109486,plain,
% 31.70/4.49      ( v4_pre_topc(sK4,k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.49      | v4_pre_topc(sK4,sK2) != iProver_top
% 31.70/4.49      | m1_subset_1(k3_xboole_0(sK4,sK3),k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 31.70/4.49      inference(superposition,[status(thm)],[c_4077,c_109478]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_109491,plain,
% 31.70/4.49      ( v4_pre_topc(sK4,k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.49      | v4_pre_topc(sK4,sK2) != iProver_top
% 31.70/4.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.49      | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top ),
% 31.70/4.49      inference(light_normalisation,[status(thm)],[c_109486,c_4077]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3034,plain,
% 31.70/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.70/4.49      | r1_tarski(X0,X1) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_30,plain,
% 31.70/4.49      ( ~ v2_compts_1(X0,X1)
% 31.70/4.49      | v2_compts_1(X0,X2)
% 31.70/4.49      | ~ m1_pre_topc(X2,X1)
% 31.70/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 31.70/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 31.70/4.49      | ~ l1_pre_topc(X1) ),
% 31.70/4.49      inference(cnf_transformation,[],[f116]) ).
% 31.70/4.49  
% 31.70/4.49  cnf(c_3017,plain,
% 31.70/4.49      ( v2_compts_1(X0,X1) != iProver_top
% 31.70/4.49      | v2_compts_1(X0,X2) = iProver_top
% 31.70/4.49      | m1_pre_topc(X2,X1) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 31.70/4.49      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 31.70/4.49      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7390,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1) = iProver_top
% 31.70/4.50      | v2_compts_1(X0,sK2) != iProver_top
% 31.70/4.50      | m1_pre_topc(X1,sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 31.70/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_4011,c_3017]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8016,plain,
% 31.70/4.50      ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.50      | m1_pre_topc(X1,sK2) != iProver_top
% 31.70/4.50      | v2_compts_1(X0,sK2) != iProver_top
% 31.70/4.50      | v2_compts_1(X0,X1) = iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_7390,c_45]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8017,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1) = iProver_top
% 31.70/4.50      | v2_compts_1(X0,sK2) != iProver_top
% 31.70/4.50      | m1_pre_topc(X1,sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_8016]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8022,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1) = iProver_top
% 31.70/4.50      | v2_compts_1(X0,sK2) != iProver_top
% 31.70/4.50      | m1_pre_topc(X1,sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 31.70/4.50      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3034,c_8017]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_93065,plain,
% 31.70/4.50      ( v2_compts_1(sK3,X0) = iProver_top
% 31.70/4.50      | v2_compts_1(sK3,sK2) != iProver_top
% 31.70/4.50      | m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | r1_tarski(sK3,u1_struct_0(X0)) != iProver_top
% 31.70/4.50      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_4261,c_8022]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_39,negated_conjecture,
% 31.70/4.50      ( v2_compts_1(sK3,sK2) ),
% 31.70/4.50      inference(cnf_transformation,[],[f106]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_48,plain,
% 31.70/4.50      ( v2_compts_1(sK3,sK2) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_557,plain,
% 31.70/4.50      ( u1_struct_0(X0) = k2_struct_0(X0)
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3377,plain,
% 31.70/4.50      ( r1_tarski(sK3,sK3) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.70/4.50      inference(cnf_transformation,[],[f69]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3481,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_1]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3864,plain,
% 31.70/4.50      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_3481]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_17,plain,
% 31.70/4.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f83]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4063,plain,
% 31.70/4.50      ( ~ m1_pre_topc(X0,sK2) | l1_pre_topc(X0) | ~ l1_pre_topc(sK2) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_17]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4064,plain,
% 31.70/4.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) = iProver_top
% 31.70/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_4063]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2144,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.70/4.50      theory(equality) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3240,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_2144]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3486,plain,
% 31.70/4.50      ( ~ r1_tarski(sK3,X0) | r1_tarski(sK3,X1) | X1 != X0 | sK3 != sK3 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_3240]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7351,plain,
% 31.70/4.50      ( ~ r1_tarski(sK3,X0)
% 31.70/4.50      | r1_tarski(sK3,u1_struct_0(X1))
% 31.70/4.50      | u1_struct_0(X1) != X0
% 31.70/4.50      | sK3 != sK3 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_3486]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_11980,plain,
% 31.70/4.50      ( r1_tarski(sK3,u1_struct_0(X0))
% 31.70/4.50      | ~ r1_tarski(sK3,k2_struct_0(X0))
% 31.70/4.50      | u1_struct_0(X0) != k2_struct_0(X0)
% 31.70/4.50      | sK3 != sK3 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_7351]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_11981,plain,
% 31.70/4.50      ( u1_struct_0(X0) != k2_struct_0(X0)
% 31.70/4.50      | sK3 != sK3
% 31.70/4.50      | r1_tarski(sK3,u1_struct_0(X0)) = iProver_top
% 31.70/4.50      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_11980]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_93972,plain,
% 31.70/4.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | v2_compts_1(sK3,X0) = iProver_top
% 31.70/4.50      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_93065,c_45,c_48,c_557,c_3377,c_3864,c_4064,c_11981]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_93973,plain,
% 31.70/4.50      ( v2_compts_1(sK3,X0) = iProver_top
% 31.70/4.50      | m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_93972]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_93982,plain,
% 31.70/4.50      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 31.70/4.50      | r1_tarski(sK3,sK3) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6061,c_93973]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_18,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
% 31.70/4.50      | ~ r1_tarski(X2,X0)
% 31.70/4.50      | ~ v2_pre_topc(X1)
% 31.70/4.50      | ~ l1_pre_topc(X1)
% 31.70/4.50      | k1_pre_topc(k1_pre_topc(X1,X0),X2) = k1_pre_topc(X1,X2) ),
% 31.70/4.50      inference(cnf_transformation,[],[f114]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_43,negated_conjecture,
% 31.70/4.50      ( v2_pre_topc(sK2) ),
% 31.70/4.50      inference(cnf_transformation,[],[f102]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_648,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
% 31.70/4.50      | ~ r1_tarski(X2,X0)
% 31.70/4.50      | ~ l1_pre_topc(X1)
% 31.70/4.50      | k1_pre_topc(k1_pre_topc(X1,X0),X2) = k1_pre_topc(X1,X2)
% 31.70/4.50      | sK2 != X1 ),
% 31.70/4.50      inference(resolution_lifted,[status(thm)],[c_18,c_43]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_649,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X1))))
% 31.70/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ r1_tarski(X0,X1)
% 31.70/4.50      | ~ l1_pre_topc(sK2)
% 31.70/4.50      | k1_pre_topc(k1_pre_topc(sK2,X1),X0) = k1_pre_topc(sK2,X0) ),
% 31.70/4.50      inference(unflattening,[status(thm)],[c_648]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_653,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1)
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X1))))
% 31.70/4.50      | k1_pre_topc(k1_pre_topc(sK2,X1),X0) = k1_pre_topc(sK2,X0) ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_649,c_42]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_654,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X1))))
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ r1_tarski(X0,X1)
% 31.70/4.50      | k1_pre_topc(k1_pre_topc(sK2,X1),X0) = k1_pre_topc(sK2,X0) ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_653]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3000,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_655,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_20,plain,
% 31.70/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.70/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 31.70/4.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ l1_pre_topc(X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f86]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3139,plain,
% 31.70/4.50      ( ~ m1_pre_topc(X0,sK2)
% 31.70/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ l1_pre_topc(sK2) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_20]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3266,plain,
% 31.70/4.50      ( ~ m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
% 31.70/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0))))
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 31.70/4.50      | ~ l1_pre_topc(sK2) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_3139]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3267,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 31.70/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_3266]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3429,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_3428]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3477,plain,
% 31.70/4.50      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
% 31.70/4.50      | k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_3000,c_45,c_655,c_3267,c_3429]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3478,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X0)))) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_3477]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4168,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top
% 31.70/4.50      | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK2,X0))) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3034,c_3478]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4169,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,X0),X1) = k1_pre_topc(sK2,X1)
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top
% 31.70/4.50      | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK2,X0))) != iProver_top ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_4168,c_4011]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5325,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,sK3),X0) = k1_pre_topc(sK2,X0)
% 31.70/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_5199,c_4169]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_17093,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,sK3),X0) = k1_pre_topc(sK2,X0)
% 31.70/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_5325,c_4261]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_17100,plain,
% 31.70/4.50      ( k1_pre_topc(k1_pre_topc(sK2,sK3),sK4) = k1_pre_topc(sK2,sK4) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3011,c_17093]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3031,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5916,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK2,sK3),X0),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.50      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_5199,c_3031]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4209,plain,
% 31.70/4.50      ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
% 31.70/4.50      | l1_pre_topc(k1_pre_topc(sK2,sK3))
% 31.70/4.50      | ~ l1_pre_topc(sK2) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_4063]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4210,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 31.70/4.50      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_4209]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_19959,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 31.70/4.50      | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK2,sK3),X0),k1_pre_topc(sK2,sK3)) = iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_5916,c_45,c_46,c_3789,c_4210]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_19960,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK2,sK3),X0),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_19959]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_19965,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_17100,c_19960]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_49,plain,
% 31.70/4.50      ( r1_tarski(sK4,sK3) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5913,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 31.70/4.50      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3034,c_3031]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_17197,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | r1_tarski(sK4,u1_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top
% 31.70/4.50      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_17100,c_5913]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_17201,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | r1_tarski(sK4,sK3) != iProver_top
% 31.70/4.50      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_17197,c_5199]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_20115,plain,
% 31.70/4.50      ( m1_pre_topc(k1_pre_topc(sK2,sK4),k1_pre_topc(sK2,sK3)) = iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_19965,c_45,c_46,c_49,c_3789,c_4210,c_17201]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_40,negated_conjecture,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 31.70/4.50      inference(cnf_transformation,[],[f105]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3009,plain,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4260,plain,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_4011,c_3009]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5198,plain,
% 31.70/4.50      ( u1_struct_0(k1_pre_topc(sK2,sK4)) = sK4 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_4260,c_5191]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7,plain,
% 31.70/4.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 31.70/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3035,plain,
% 31.70/4.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6,plain,
% 31.70/4.50      ( k2_subset_1(X0) = X0 ),
% 31.70/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3039,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_3035,c_6]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3027,plain,
% 31.70/4.50      ( m1_pre_topc(X0,X1) != iProver_top
% 31.70/4.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 31.70/4.50      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6544,plain,
% 31.70/4.50      ( m1_pre_topc(X0,X1) != iProver_top
% 31.70/4.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 31.70/4.50      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3039,c_3027]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_35,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1)
% 31.70/4.50      | ~ v4_pre_topc(X0,X1)
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ v1_compts_1(X1)
% 31.70/4.50      | ~ l1_pre_topc(X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f101]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3014,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1) = iProver_top
% 31.70/4.50      | v4_pre_topc(X0,X1) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.50      | v1_compts_1(X1) != iProver_top
% 31.70/4.50      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_15745,plain,
% 31.70/4.50      ( v2_compts_1(u1_struct_0(X0),X1) = iProver_top
% 31.70/4.50      | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 31.70/4.50      | m1_pre_topc(X0,X1) != iProver_top
% 31.70/4.50      | v1_compts_1(X1) != iProver_top
% 31.70/4.50      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6544,c_3014]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_39816,plain,
% 31.70/4.50      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK4)),X0) = iProver_top
% 31.70/4.50      | v4_pre_topc(sK4,X0) != iProver_top
% 31.70/4.50      | m1_pre_topc(k1_pre_topc(sK2,sK4),X0) != iProver_top
% 31.70/4.50      | v1_compts_1(X0) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_5198,c_15745]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_39819,plain,
% 31.70/4.50      ( v2_compts_1(sK4,X0) = iProver_top
% 31.70/4.50      | v4_pre_topc(sK4,X0) != iProver_top
% 31.70/4.50      | m1_pre_topc(k1_pre_topc(sK2,sK4),X0) != iProver_top
% 31.70/4.50      | v1_compts_1(X0) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_39816,c_5198]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_40050,plain,
% 31.70/4.50      ( v2_compts_1(sK4,k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | v4_pre_topc(sK4,k1_pre_topc(sK2,sK3)) != iProver_top
% 31.70/4.50      | v1_compts_1(k1_pre_topc(sK2,sK3)) != iProver_top
% 31.70/4.50      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_20115,c_39819]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_28,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1)
% 31.70/4.50      | ~ m1_pre_topc(X2,X1)
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ r1_tarski(X0,k2_struct_0(X2))
% 31.70/4.50      | ~ l1_pre_topc(X1)
% 31.70/4.50      | sK1(X2,X0) = X0 ),
% 31.70/4.50      inference(cnf_transformation,[],[f95]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3019,plain,
% 31.70/4.50      ( sK1(X0,X1) = X1
% 31.70/4.50      | v2_compts_1(X1,X2) = iProver_top
% 31.70/4.50      | m1_pre_topc(X0,X2) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 31.70/4.50      | l1_pre_topc(X2) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7717,plain,
% 31.70/4.50      ( sK1(X0,X1) = X1
% 31.70/4.50      | v2_compts_1(X1,sK2) = iProver_top
% 31.70/4.50      | m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 31.70/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_4011,c_3019]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8398,plain,
% 31.70/4.50      ( r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | v2_compts_1(X1,sK2) = iProver_top
% 31.70/4.50      | sK1(X0,X1) = X1 ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_7717,c_45]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8399,plain,
% 31.70/4.50      ( sK1(X0,X1) = X1
% 31.70/4.50      | v2_compts_1(X1,sK2) = iProver_top
% 31.70/4.50      | m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_8398]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8406,plain,
% 31.70/4.50      ( sK1(X0,sK4) = sK4
% 31.70/4.50      | v2_compts_1(sK4,sK2) = iProver_top
% 31.70/4.50      | m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | r1_tarski(sK4,k2_struct_0(X0)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_4260,c_8399]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_36,negated_conjecture,
% 31.70/4.50      ( ~ v2_compts_1(sK4,sK2) ),
% 31.70/4.50      inference(cnf_transformation,[],[f109]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_51,plain,
% 31.70/4.50      ( v2_compts_1(sK4,sK2) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9121,plain,
% 31.70/4.50      ( sK1(X0,sK4) = sK4
% 31.70/4.50      | m1_pre_topc(X0,sK2) != iProver_top
% 31.70/4.50      | r1_tarski(sK4,k2_struct_0(X0)) != iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_8406,c_51]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9129,plain,
% 31.70/4.50      ( sK1(k1_pre_topc(sK2,sK3),sK4) = sK4
% 31.70/4.50      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 31.70/4.50      | r1_tarski(sK4,sK3) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6061,c_9121]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_13500,plain,
% 31.70/4.50      ( sK1(k1_pre_topc(sK2,sK3),sK4) = sK4 ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_9129,c_45,c_46,c_49,c_3789]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_27,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1)
% 31.70/4.50      | ~ v2_compts_1(sK1(X2,X0),X2)
% 31.70/4.50      | ~ m1_pre_topc(X2,X1)
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ r1_tarski(X0,k2_struct_0(X2))
% 31.70/4.50      | ~ l1_pre_topc(X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f96]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3020,plain,
% 31.70/4.50      ( v2_compts_1(X0,X1) = iProver_top
% 31.70/4.50      | v2_compts_1(sK1(X2,X0),X2) != iProver_top
% 31.70/4.50      | m1_pre_topc(X2,X1) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.70/4.50      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 31.70/4.50      | l1_pre_topc(X1) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7750,plain,
% 31.70/4.50      ( v2_compts_1(X0,sK2) = iProver_top
% 31.70/4.50      | v2_compts_1(sK1(X1,X0),X1) != iProver_top
% 31.70/4.50      | m1_pre_topc(X1,sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 31.70/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_4011,c_3020]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7912,plain,
% 31.70/4.50      ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | m1_pre_topc(X1,sK2) != iProver_top
% 31.70/4.50      | v2_compts_1(sK1(X1,X0),X1) != iProver_top
% 31.70/4.50      | v2_compts_1(X0,sK2) = iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_7750,c_45]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7913,plain,
% 31.70/4.50      ( v2_compts_1(X0,sK2) = iProver_top
% 31.70/4.50      | v2_compts_1(sK1(X1,X0),X1) != iProver_top
% 31.70/4.50      | m1_pre_topc(X1,sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_7912]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_13503,plain,
% 31.70/4.50      ( v2_compts_1(sK4,k1_pre_topc(sK2,sK3)) != iProver_top
% 31.70/4.50      | v2_compts_1(sK4,sK2) = iProver_top
% 31.70/4.50      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(sK4,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_13500,c_7913]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_13504,plain,
% 31.70/4.50      ( v2_compts_1(sK4,k1_pre_topc(sK2,sK3)) != iProver_top
% 31.70/4.50      | v2_compts_1(sK4,sK2) = iProver_top
% 31.70/4.50      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 31.70/4.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 31.70/4.50      | r1_tarski(sK4,sK3) != iProver_top ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_13503,c_6061]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_25,plain,
% 31.70/4.50      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 31.70/4.50      | v1_compts_1(X0)
% 31.70/4.50      | ~ l1_pre_topc(X0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f92]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3022,plain,
% 31.70/4.50      ( v2_compts_1(k2_struct_0(X0),X0) != iProver_top
% 31.70/4.50      | v1_compts_1(X0) = iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6234,plain,
% 31.70/4.50      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 31.70/4.50      | v1_compts_1(k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6061,c_3022]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_13239,plain,
% 31.70/4.50      ( v1_compts_1(k1_pre_topc(sK2,sK3)) = iProver_top
% 31.70/4.50      | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_6234,c_45,c_46,c_3789,c_4210]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_13240,plain,
% 31.70/4.50      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 31.70/4.50      | v1_compts_1(k1_pre_topc(sK2,sK3)) = iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_13239]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_10,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f75]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3033,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.70/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4157,plain,
% 31.70/4.50      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3009,c_3033]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4161,plain,
% 31.70/4.50      ( r1_tarski(sK4,k2_struct_0(sK2)) = iProver_top ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_4157,c_4011]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3395,plain,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~ r1_tarski(sK4,X0) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_9]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3744,plain,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) | ~ r1_tarski(sK4,sK3) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_3395]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3745,plain,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top
% 31.70/4.50      | r1_tarski(sK4,sK3) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_3744]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3378,plain,
% 31.70/4.50      ( r1_tarski(sK3,sK3) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_3377]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3355,plain,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2)))
% 31.70/4.50      | ~ r1_tarski(sK4,k2_struct_0(sK2)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_9]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3356,plain,
% 31.70/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 31.70/4.50      | r1_tarski(sK4,k2_struct_0(sK2)) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_3355]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_37,negated_conjecture,
% 31.70/4.50      ( v4_pre_topc(sK4,sK2) ),
% 31.70/4.50      inference(cnf_transformation,[],[f108]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_50,plain,
% 31.70/4.50      ( v4_pre_topc(sK4,sK2) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(contradiction,plain,
% 31.70/4.50      ( $false ),
% 31.70/4.50      inference(minisat,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_109491,c_93982,c_40050,c_13504,c_13240,c_4210,c_4161,
% 31.70/4.50                 c_3789,c_3745,c_3378,c_3356,c_51,c_50,c_49,c_46,c_45]) ).
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.70/4.50  
% 31.70/4.50  ------                               Statistics
% 31.70/4.50  
% 31.70/4.50  ------ General
% 31.70/4.50  
% 31.70/4.50  abstr_ref_over_cycles:                  0
% 31.70/4.50  abstr_ref_under_cycles:                 0
% 31.70/4.50  gc_basic_clause_elim:                   0
% 31.70/4.50  forced_gc_time:                         0
% 31.70/4.50  parsing_time:                           0.013
% 31.70/4.50  unif_index_cands_time:                  0.
% 31.70/4.50  unif_index_add_time:                    0.
% 31.70/4.50  orderings_time:                         0.
% 31.70/4.50  out_proof_time:                         0.037
% 31.70/4.50  total_time:                             3.849
% 31.70/4.50  num_of_symbols:                         54
% 31.70/4.50  num_of_terms:                           82810
% 31.70/4.50  
% 31.70/4.50  ------ Preprocessing
% 31.70/4.50  
% 31.70/4.50  num_of_splits:                          0
% 31.70/4.50  num_of_split_atoms:                     0
% 31.70/4.50  num_of_reused_defs:                     0
% 31.70/4.50  num_eq_ax_congr_red:                    28
% 31.70/4.50  num_of_sem_filtered_clauses:            1
% 31.70/4.50  num_of_subtypes:                        0
% 31.70/4.50  monotx_restored_types:                  0
% 31.70/4.50  sat_num_of_epr_types:                   0
% 31.70/4.50  sat_num_of_non_cyclic_types:            0
% 31.70/4.50  sat_guarded_non_collapsed_types:        0
% 31.70/4.50  num_pure_diseq_elim:                    0
% 31.70/4.50  simp_replaced_by:                       0
% 31.70/4.50  res_preprocessed:                       197
% 31.70/4.50  prep_upred:                             0
% 31.70/4.50  prep_unflattend:                        63
% 31.70/4.50  smt_new_axioms:                         0
% 31.70/4.50  pred_elim_cands:                        8
% 31.70/4.50  pred_elim:                              2
% 31.70/4.50  pred_elim_cl:                           2
% 31.70/4.50  pred_elim_cycles:                       8
% 31.70/4.50  merged_defs:                            8
% 31.70/4.50  merged_defs_ncl:                        0
% 31.70/4.50  bin_hyper_res:                          10
% 31.70/4.50  prep_cycles:                            4
% 31.70/4.50  pred_elim_time:                         0.025
% 31.70/4.50  splitting_time:                         0.
% 31.70/4.50  sem_filter_time:                        0.
% 31.70/4.50  monotx_time:                            0.001
% 31.70/4.50  subtype_inf_time:                       0.
% 31.70/4.50  
% 31.70/4.50  ------ Problem properties
% 31.70/4.50  
% 31.70/4.50  clauses:                                41
% 31.70/4.50  conjectures:                            7
% 31.70/4.50  epr:                                    8
% 31.70/4.50  horn:                                   37
% 31.70/4.50  ground:                                 7
% 31.70/4.50  unary:                                  11
% 31.70/4.50  binary:                                 6
% 31.70/4.50  lits:                                   128
% 31.70/4.50  lits_eq:                                15
% 31.70/4.50  fd_pure:                                0
% 31.70/4.50  fd_pseudo:                              0
% 31.70/4.50  fd_cond:                                2
% 31.70/4.50  fd_pseudo_cond:                         1
% 31.70/4.50  ac_symbols:                             0
% 31.70/4.50  
% 31.70/4.50  ------ Propositional Solver
% 31.70/4.50  
% 31.70/4.50  prop_solver_calls:                      57
% 31.70/4.50  prop_fast_solver_calls:                 6384
% 31.70/4.50  smt_solver_calls:                       0
% 31.70/4.50  smt_fast_solver_calls:                  0
% 31.70/4.50  prop_num_of_clauses:                    56035
% 31.70/4.50  prop_preprocess_simplified:             71642
% 31.70/4.50  prop_fo_subsumed:                       424
% 31.70/4.50  prop_solver_time:                       0.
% 31.70/4.50  smt_solver_time:                        0.
% 31.70/4.50  smt_fast_solver_time:                   0.
% 31.70/4.50  prop_fast_solver_time:                  0.
% 31.70/4.50  prop_unsat_core_time:                   0.005
% 31.70/4.50  
% 31.70/4.50  ------ QBF
% 31.70/4.50  
% 31.70/4.50  qbf_q_res:                              0
% 31.70/4.50  qbf_num_tautologies:                    0
% 31.70/4.50  qbf_prep_cycles:                        0
% 31.70/4.50  
% 31.70/4.50  ------ BMC1
% 31.70/4.50  
% 31.70/4.50  bmc1_current_bound:                     -1
% 31.70/4.50  bmc1_last_solved_bound:                 -1
% 31.70/4.50  bmc1_unsat_core_size:                   -1
% 31.70/4.50  bmc1_unsat_core_parents_size:           -1
% 31.70/4.50  bmc1_merge_next_fun:                    0
% 31.70/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.70/4.50  
% 31.70/4.50  ------ Instantiation
% 31.70/4.50  
% 31.70/4.50  inst_num_of_clauses:                    5405
% 31.70/4.50  inst_num_in_passive:                    1232
% 31.70/4.50  inst_num_in_active:                     4900
% 31.70/4.50  inst_num_in_unprocessed:                2087
% 31.70/4.50  inst_num_of_loops:                      5269
% 31.70/4.50  inst_num_of_learning_restarts:          1
% 31.70/4.50  inst_num_moves_active_passive:          368
% 31.70/4.50  inst_lit_activity:                      0
% 31.70/4.50  inst_lit_activity_moves:                4
% 31.70/4.50  inst_num_tautologies:                   0
% 31.70/4.50  inst_num_prop_implied:                  0
% 31.70/4.50  inst_num_existing_simplified:           0
% 31.70/4.50  inst_num_eq_res_simplified:             0
% 31.70/4.50  inst_num_child_elim:                    0
% 31.70/4.50  inst_num_of_dismatching_blockings:      8576
% 31.70/4.50  inst_num_of_non_proper_insts:           14023
% 31.70/4.50  inst_num_of_duplicates:                 0
% 31.70/4.50  inst_inst_num_from_inst_to_res:         0
% 31.70/4.50  inst_dismatching_checking_time:         0.
% 31.70/4.50  
% 31.70/4.50  ------ Resolution
% 31.70/4.50  
% 31.70/4.50  res_num_of_clauses:                     56
% 31.70/4.50  res_num_in_passive:                     56
% 31.70/4.50  res_num_in_active:                      0
% 31.70/4.50  res_num_of_loops:                       201
% 31.70/4.50  res_forward_subset_subsumed:            1130
% 31.70/4.50  res_backward_subset_subsumed:           2
% 31.70/4.50  res_forward_subsumed:                   0
% 31.70/4.50  res_backward_subsumed:                  0
% 31.70/4.50  res_forward_subsumption_resolution:     1
% 31.70/4.50  res_backward_subsumption_resolution:    0
% 31.70/4.50  res_clause_to_clause_subsumption:       41074
% 31.70/4.50  res_orphan_elimination:                 0
% 31.70/4.50  res_tautology_del:                      666
% 31.70/4.50  res_num_eq_res_simplified:              0
% 31.70/4.50  res_num_sel_changes:                    0
% 31.70/4.50  res_moves_from_active_to_pass:          0
% 31.70/4.50  
% 31.70/4.50  ------ Superposition
% 31.70/4.50  
% 31.70/4.50  sup_time_total:                         0.
% 31.70/4.50  sup_time_generating:                    0.
% 31.70/4.50  sup_time_sim_full:                      0.
% 31.70/4.50  sup_time_sim_immed:                     0.
% 31.70/4.50  
% 31.70/4.50  sup_num_of_clauses:                     6646
% 31.70/4.50  sup_num_in_active:                      987
% 31.70/4.50  sup_num_in_passive:                     5659
% 31.70/4.50  sup_num_of_loops:                       1053
% 31.70/4.50  sup_fw_superposition:                   6052
% 31.70/4.50  sup_bw_superposition:                   5976
% 31.70/4.50  sup_immediate_simplified:               3952
% 31.70/4.50  sup_given_eliminated:                   2
% 31.70/4.50  comparisons_done:                       0
% 31.70/4.50  comparisons_avoided:                    0
% 31.70/4.50  
% 31.70/4.50  ------ Simplifications
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  sim_fw_subset_subsumed:                 2197
% 31.70/4.50  sim_bw_subset_subsumed:                 112
% 31.70/4.50  sim_fw_subsumed:                        953
% 31.70/4.50  sim_bw_subsumed:                        62
% 31.70/4.50  sim_fw_subsumption_res:                 0
% 31.70/4.50  sim_bw_subsumption_res:                 0
% 31.70/4.50  sim_tautology_del:                      148
% 31.70/4.50  sim_eq_tautology_del:                   203
% 31.70/4.50  sim_eq_res_simp:                        0
% 31.70/4.50  sim_fw_demodulated:                     82
% 31.70/4.50  sim_bw_demodulated:                     55
% 31.70/4.50  sim_light_normalised:                   1550
% 31.70/4.50  sim_joinable_taut:                      0
% 31.70/4.50  sim_joinable_simp:                      0
% 31.70/4.50  sim_ac_normalised:                      0
% 31.70/4.50  sim_smt_subsumption:                    0
% 31.70/4.50  
%------------------------------------------------------------------------------
