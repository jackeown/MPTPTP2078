%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1363+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:33 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  171 (1089 expanded)
%              Number of clauses        :  115 ( 315 expanded)
%              Number of leaves         :   18 ( 287 expanded)
%              Depth                    :   16
%              Number of atoms          :  760 (6938 expanded)
%              Number of equality atoms :  244 ( 632 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & v4_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & v2_compts_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK3,X0)
        & v4_pre_topc(sK3,X0)
        & r1_tarski(sK3,X1)
        & v2_compts_1(X1,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
            & r1_tarski(X2,sK2)
            & v2_compts_1(sK2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
              ( ~ v2_compts_1(X2,sK1)
              & v4_pre_topc(X2,sK1)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v2_compts_1(sK3,sK1)
    & v4_pre_topc(sK3,sK1)
    & r1_tarski(sK3,sK2)
    & v2_compts_1(sK2,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f33,f32,f31])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK0(X1,X2),X1)
        & sK0(X1,X2) = X2
        & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK0(X1,X2),X1)
                    & sK0(X1,X2) = X2
                    & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK0(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK0(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0] :
      ( v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f56,plain,(
    v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1288,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1754,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_134,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_3,c_2])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_1286,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(k1_pre_topc(X0_47,X0_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_135])).

cnf(c_1756,plain,
    ( k2_struct_0(k1_pre_topc(X0_47,X0_46)) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_2978,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_1756])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1975,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_3217,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2978,c_21,c_20,c_1975])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | v2_compts_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_362,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_363,plain,
    ( v2_compts_1(sK3,X0)
    | m1_subset_1(sK0(X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k2_struct_0(X1) != sK2 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1282,plain,
    ( v2_compts_1(sK3,X0_47)
    | m1_subset_1(sK0(X1_47,sK3),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(X1_47) != sK2 ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_1760,plain,
    ( k2_struct_0(X0_47) != sK2
    | v2_compts_1(sK3,X1_47) = iProver_top
    | m1_subset_1(sK0(X0_47,sK3),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_3220,plain,
    ( v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_1760])).

cnf(c_24,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,negated_conjecture,
    ( ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,plain,
    ( v2_compts_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1299,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | m1_pre_topc(k1_pre_topc(X0_47,X0_46),X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1985,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_1986,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1985])).

cnf(c_2058,plain,
    ( v2_compts_1(sK3,X0_47)
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_2064,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2058])).

cnf(c_2066,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2064])).

cnf(c_3685,plain,
    ( m1_subset_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3220,c_21,c_24,c_20,c_25,c_26,c_30,c_1975,c_1986,c_2066])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | v2_compts_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | sK0(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_386,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X2,X0) = X0
    | k2_struct_0(X2) != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_387,plain,
    ( v2_compts_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK0(X1,sK3) = sK3
    | k2_struct_0(X1) != sK2 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_1281,plain,
    ( v2_compts_1(sK3,X0_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK0(X1_47,sK3) = sK3
    | k2_struct_0(X1_47) != sK2 ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_1761,plain,
    ( sK0(X0_47,sK3) = sK3
    | k2_struct_0(X0_47) != sK2
    | v2_compts_1(sK3,X1_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1281])).

cnf(c_3221,plain,
    ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_1761])).

cnf(c_2059,plain,
    ( v2_compts_1(sK3,X0_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2061,plain,
    ( v2_compts_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2059])).

cnf(c_3621,plain,
    ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3221,c_21,c_20,c_19,c_15,c_1975,c_1985,c_2061])).

cnf(c_3689,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3685,c_3621])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | v2_compts_1(X0,X2)
    | ~ v2_compts_1(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_410,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK0(X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_411,plain,
    ( ~ v2_compts_1(sK0(X0,sK3),X0)
    | v2_compts_1(sK3,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1280,plain,
    ( ~ v2_compts_1(sK0(X0_47,sK3),X0_47)
    | v2_compts_1(sK3,X1_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | k2_struct_0(X0_47) != sK2 ),
    inference(subtyping,[status(esa)],[c_411])).

cnf(c_1762,plain,
    ( k2_struct_0(X0_47) != sK2
    | v2_compts_1(sK0(X0_47,sK3),X0_47) != iProver_top
    | v2_compts_1(sK3,X1_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1_47))) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_3223,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_1762])).

cnf(c_2053,plain,
    ( ~ v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2))
    | v2_compts_1(sK3,X0_47)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47)
    | ~ l1_pre_topc(X0_47)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_2054,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,X0_47) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2053])).

cnf(c_2056,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_3434,plain,
    ( v2_compts_1(sK0(k1_pre_topc(sK1,sK2),sK3),k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3223,c_21,c_24,c_20,c_25,c_26,c_30,c_1975,c_1986,c_2056])).

cnf(c_3624,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3621,c_3434])).

cnf(c_1318,plain,
    ( ~ v1_compts_1(X0_47)
    | v1_compts_1(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_2407,plain,
    ( v1_compts_1(X0_47)
    | ~ v1_compts_1(k1_pre_topc(X1_47,k1_xboole_0))
    | X0_47 != k1_pre_topc(X1_47,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_2576,plain,
    ( v1_compts_1(k1_pre_topc(X0_47,X0_46))
    | ~ v1_compts_1(k1_pre_topc(X1_47,k1_xboole_0))
    | k1_pre_topc(X0_47,X0_46) != k1_pre_topc(X1_47,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_3562,plain,
    ( ~ v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0))
    | v1_compts_1(k1_pre_topc(sK1,sK2))
    | k1_pre_topc(sK1,sK2) != k1_pre_topc(X0_47,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2576])).

cnf(c_3563,plain,
    ( k1_pre_topc(sK1,sK2) != k1_pre_topc(X0_47,k1_xboole_0)
    | v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0)) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3562])).

cnf(c_3565,plain,
    ( k1_pre_topc(sK1,sK2) != k1_pre_topc(sK1,k1_xboole_0)
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top
    | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3563])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1293,plain,
    ( ~ v4_pre_topc(X0_46,X0_47)
    | v4_pre_topc(X0_46,X1_47)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2008,plain,
    ( v4_pre_topc(sK3,X0_47)
    | ~ v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0_47,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_2877,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_2880,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2877])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1294,plain,
    ( ~ v4_pre_topc(X0_46,X0_47)
    | v2_compts_1(X0_46,X0_47)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ v1_compts_1(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2671,plain,
    ( ~ v4_pre_topc(X0_46,k1_pre_topc(sK1,sK2))
    | v2_compts_1(X0_46,k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_2875,plain,
    ( ~ v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
    | v2_compts_1(sK3,k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_2878,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) != iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK1,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2)))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2875])).

cnf(c_1309,plain,
    ( X0_47 != X1_47
    | k1_pre_topc(X0_47,X0_46) = k1_pre_topc(X1_47,X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_2706,plain,
    ( k1_pre_topc(sK1,sK2) = k1_pre_topc(X0_47,X0_46)
    | sK1 != X0_47
    | sK2 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_2708,plain,
    ( k1_pre_topc(sK1,sK2) = k1_pre_topc(sK1,k1_xboole_0)
    | sK1 != sK1
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2706])).

cnf(c_10,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_compts_1(k1_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_279,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_compts_1(k1_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_280,plain,
    ( ~ v2_compts_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0))
    | ~ l1_pre_topc(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_284,plain,
    ( v1_compts_1(k1_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_compts_1(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_21])).

cnf(c_285,plain,
    ( ~ v2_compts_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_1285,plain,
    ( ~ v2_compts_1(X0_46,sK1)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,X0_46))
    | k1_xboole_0 = X0_46 ),
    inference(subtyping,[status(esa)],[c_285])).

cnf(c_1757,plain,
    ( k1_xboole_0 = X0_46
    | v2_compts_1(X0_46,sK1) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1285])).

cnf(c_2431,plain,
    ( sK2 = k1_xboole_0
    | v2_compts_1(sK2,sK1) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_1757])).

cnf(c_18,negated_conjecture,
    ( v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,plain,
    ( v2_compts_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2495,plain,
    ( sK2 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2431,c_27])).

cnf(c_1743,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_47,X0_46),X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_2207,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_1743])).

cnf(c_2418,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2207,c_24,c_25,c_1986])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1297,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1745,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_2423,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2418,c_1745])).

cnf(c_1304,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2164,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1314,plain,
    ( ~ m1_subset_1(X0_46,X0_48)
    | m1_subset_1(X1_46,X1_48)
    | X1_48 != X0_48
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1993,plain,
    ( m1_subset_1(X0_46,X0_48)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_48 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_2163,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_2165,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_46 != sK2
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2163])).

cnf(c_2167,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | k1_xboole_0 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_2105,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_compts_1(k1_pre_topc(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_2109,plain,
    ( k1_xboole_0 = sK2
    | v2_compts_1(sK2,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_1316,plain,
    ( ~ v2_compts_1(X0_46,X0_47)
    | v2_compts_1(X1_46,X1_47)
    | X1_47 != X0_47
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1998,plain,
    ( v2_compts_1(X0_46,X0_47)
    | ~ v2_compts_1(sK2,sK1)
    | X0_47 != sK1
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_1999,plain,
    ( X0_47 != sK1
    | X0_46 != sK2
    | v2_compts_1(X0_46,X0_47) = iProver_top
    | v2_compts_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2001,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | v2_compts_1(sK2,sK1) != iProver_top
    | v2_compts_1(k1_xboole_0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_12,plain,
    ( ~ v2_compts_1(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1295,plain,
    ( ~ v2_compts_1(k1_xboole_0,X0_47)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_47)))
    | v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1350,plain,
    ( v2_compts_1(k1_xboole_0,X0_47) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | v1_compts_1(k1_pre_topc(X0_47,k1_xboole_0)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_1352,plain,
    ( v2_compts_1(k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,k1_xboole_0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_1303,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1334,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3689,c_3624,c_3565,c_2880,c_2878,c_2708,c_2495,c_2423,c_2164,c_2167,c_2109,c_2001,c_1986,c_1352,c_1334,c_29,c_27,c_26,c_25,c_24])).


%------------------------------------------------------------------------------
