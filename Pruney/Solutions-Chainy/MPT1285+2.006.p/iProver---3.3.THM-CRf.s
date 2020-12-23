%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:53 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 803 expanded)
%              Number of clauses        :   99 ( 212 expanded)
%              Number of leaves         :   15 ( 265 expanded)
%              Depth                    :   16
%              Number of atoms          :  609 (7038 expanded)
%              Number of equality atoms :  130 ( 245 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(X2,X0)
                | ~ v3_pre_topc(X2,X0) )
              & v6_tops_1(X2,X0) )
            | ( ~ v6_tops_1(X3,X1)
              & v4_tops_1(X3,X1)
              & v3_pre_topc(X3,X1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ( ( ~ v4_tops_1(X2,X0)
              | ~ v3_pre_topc(X2,X0) )
            & v6_tops_1(X2,X0) )
          | ( ~ v6_tops_1(sK3,X1)
            & v4_tops_1(sK3,X1)
            & v3_pre_topc(sK3,X1) ) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,X0)
                    | ~ v3_pre_topc(X2,X0) )
                  & v6_tops_1(X2,X0) )
                | ( ~ v6_tops_1(X3,X1)
                  & v4_tops_1(X3,X1)
                  & v3_pre_topc(X3,X1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(sK2,X0)
                  | ~ v3_pre_topc(sK2,X0) )
                & v6_tops_1(sK2,X0) )
              | ( ~ v6_tops_1(X3,X1)
                & v4_tops_1(X3,X1)
                & v3_pre_topc(X3,X1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,X0)
                      | ~ v3_pre_topc(X2,X0) )
                    & v6_tops_1(X2,X0) )
                  | ( ~ v6_tops_1(X3,sK1)
                    & v4_tops_1(X3,sK1)
                    & v3_pre_topc(X3,sK1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f38,f37,f36,f35])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4532,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_1223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_2046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1223])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1243,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_459,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_460,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1230,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_3643,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1230])).

cnf(c_3778,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_3643])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1251,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3883,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3778,c_1251])).

cnf(c_4467,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_3883])).

cnf(c_4474,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4467])).

cnf(c_20,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1245,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1244,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_294,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_295,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_1241,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_3298,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1241])).

cnf(c_3585,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_3298])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_31,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( ~ v6_tops_1(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,plain,
    ( v6_tops_1(sK3,sK1) != iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1340,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_1341,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1340])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1352,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_1353,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1352])).

cnf(c_9,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_357,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_358,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1370,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_1371,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
    | v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1497,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1498,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1497])).

cnf(c_8,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_372,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_373,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_1507,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_1508,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1507])).

cnf(c_309,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_310,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_1512,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_3623,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_3624,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3623])).

cnf(c_3772,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3585,c_30,c_31,c_32,c_33,c_1341,c_1353,c_1371,c_1498,c_1508,c_3624])).

cnf(c_10,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_492,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_493,plain,
    ( ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_1228,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
    | v6_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_2517,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1228])).

cnf(c_3776,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3772,c_2517])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_1222,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_12,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_273,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_274,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_24])).

cnf(c_279,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_1242,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_1947,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1242])).

cnf(c_4186,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3776,c_1947])).

cnf(c_4187,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4186])).

cnf(c_6,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_552,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_553,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_1224,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_4183,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3776,c_1224])).

cnf(c_4184,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4183])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4532,c_4474,c_4187,c_4184,c_3623,c_1507,c_1497,c_1370,c_1352,c_1340,c_15,c_16,c_17,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.20/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.01  
% 3.20/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/1.01  
% 3.20/1.01  ------  iProver source info
% 3.20/1.01  
% 3.20/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.20/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/1.01  git: non_committed_changes: false
% 3.20/1.01  git: last_make_outside_of_git: false
% 3.20/1.01  
% 3.20/1.01  ------ 
% 3.20/1.01  
% 3.20/1.01  ------ Input Options
% 3.20/1.01  
% 3.20/1.01  --out_options                           all
% 3.20/1.01  --tptp_safe_out                         true
% 3.20/1.01  --problem_path                          ""
% 3.20/1.01  --include_path                          ""
% 3.20/1.01  --clausifier                            res/vclausify_rel
% 3.20/1.01  --clausifier_options                    ""
% 3.20/1.01  --stdin                                 false
% 3.20/1.01  --stats_out                             all
% 3.20/1.01  
% 3.20/1.01  ------ General Options
% 3.20/1.01  
% 3.20/1.01  --fof                                   false
% 3.20/1.01  --time_out_real                         305.
% 3.20/1.01  --time_out_virtual                      -1.
% 3.20/1.01  --symbol_type_check                     false
% 3.20/1.01  --clausify_out                          false
% 3.20/1.01  --sig_cnt_out                           false
% 3.20/1.01  --trig_cnt_out                          false
% 3.20/1.01  --trig_cnt_out_tolerance                1.
% 3.20/1.01  --trig_cnt_out_sk_spl                   false
% 3.20/1.01  --abstr_cl_out                          false
% 3.20/1.01  
% 3.20/1.01  ------ Global Options
% 3.20/1.01  
% 3.20/1.01  --schedule                              default
% 3.20/1.01  --add_important_lit                     false
% 3.20/1.01  --prop_solver_per_cl                    1000
% 3.20/1.01  --min_unsat_core                        false
% 3.20/1.01  --soft_assumptions                      false
% 3.20/1.01  --soft_lemma_size                       3
% 3.20/1.01  --prop_impl_unit_size                   0
% 3.20/1.01  --prop_impl_unit                        []
% 3.20/1.01  --share_sel_clauses                     true
% 3.20/1.01  --reset_solvers                         false
% 3.20/1.01  --bc_imp_inh                            [conj_cone]
% 3.20/1.01  --conj_cone_tolerance                   3.
% 3.20/1.01  --extra_neg_conj                        none
% 3.20/1.01  --large_theory_mode                     true
% 3.20/1.01  --prolific_symb_bound                   200
% 3.20/1.01  --lt_threshold                          2000
% 3.20/1.01  --clause_weak_htbl                      true
% 3.20/1.01  --gc_record_bc_elim                     false
% 3.20/1.01  
% 3.20/1.01  ------ Preprocessing Options
% 3.20/1.01  
% 3.20/1.01  --preprocessing_flag                    true
% 3.20/1.01  --time_out_prep_mult                    0.1
% 3.20/1.01  --splitting_mode                        input
% 3.20/1.01  --splitting_grd                         true
% 3.20/1.01  --splitting_cvd                         false
% 3.20/1.01  --splitting_cvd_svl                     false
% 3.20/1.01  --splitting_nvd                         32
% 3.20/1.01  --sub_typing                            true
% 3.20/1.01  --prep_gs_sim                           true
% 3.20/1.01  --prep_unflatten                        true
% 3.20/1.01  --prep_res_sim                          true
% 3.20/1.01  --prep_upred                            true
% 3.20/1.01  --prep_sem_filter                       exhaustive
% 3.20/1.01  --prep_sem_filter_out                   false
% 3.20/1.01  --pred_elim                             true
% 3.20/1.01  --res_sim_input                         true
% 3.20/1.01  --eq_ax_congr_red                       true
% 3.20/1.01  --pure_diseq_elim                       true
% 3.20/1.01  --brand_transform                       false
% 3.20/1.01  --non_eq_to_eq                          false
% 3.20/1.01  --prep_def_merge                        true
% 3.20/1.01  --prep_def_merge_prop_impl              false
% 3.20/1.01  --prep_def_merge_mbd                    true
% 3.20/1.01  --prep_def_merge_tr_red                 false
% 3.20/1.01  --prep_def_merge_tr_cl                  false
% 3.20/1.01  --smt_preprocessing                     true
% 3.20/1.01  --smt_ac_axioms                         fast
% 3.20/1.01  --preprocessed_out                      false
% 3.20/1.01  --preprocessed_stats                    false
% 3.20/1.01  
% 3.20/1.01  ------ Abstraction refinement Options
% 3.20/1.01  
% 3.20/1.01  --abstr_ref                             []
% 3.20/1.01  --abstr_ref_prep                        false
% 3.20/1.01  --abstr_ref_until_sat                   false
% 3.20/1.01  --abstr_ref_sig_restrict                funpre
% 3.20/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.01  --abstr_ref_under                       []
% 3.20/1.01  
% 3.20/1.01  ------ SAT Options
% 3.20/1.01  
% 3.20/1.01  --sat_mode                              false
% 3.20/1.01  --sat_fm_restart_options                ""
% 3.20/1.01  --sat_gr_def                            false
% 3.20/1.01  --sat_epr_types                         true
% 3.20/1.01  --sat_non_cyclic_types                  false
% 3.20/1.01  --sat_finite_models                     false
% 3.20/1.01  --sat_fm_lemmas                         false
% 3.20/1.01  --sat_fm_prep                           false
% 3.20/1.01  --sat_fm_uc_incr                        true
% 3.20/1.01  --sat_out_model                         small
% 3.20/1.01  --sat_out_clauses                       false
% 3.20/1.01  
% 3.20/1.01  ------ QBF Options
% 3.20/1.01  
% 3.20/1.01  --qbf_mode                              false
% 3.20/1.01  --qbf_elim_univ                         false
% 3.20/1.01  --qbf_dom_inst                          none
% 3.20/1.01  --qbf_dom_pre_inst                      false
% 3.20/1.01  --qbf_sk_in                             false
% 3.20/1.01  --qbf_pred_elim                         true
% 3.20/1.01  --qbf_split                             512
% 3.20/1.01  
% 3.20/1.01  ------ BMC1 Options
% 3.20/1.01  
% 3.20/1.01  --bmc1_incremental                      false
% 3.20/1.01  --bmc1_axioms                           reachable_all
% 3.20/1.01  --bmc1_min_bound                        0
% 3.20/1.01  --bmc1_max_bound                        -1
% 3.20/1.01  --bmc1_max_bound_default                -1
% 3.20/1.01  --bmc1_symbol_reachability              true
% 3.20/1.01  --bmc1_property_lemmas                  false
% 3.20/1.01  --bmc1_k_induction                      false
% 3.20/1.01  --bmc1_non_equiv_states                 false
% 3.20/1.01  --bmc1_deadlock                         false
% 3.20/1.01  --bmc1_ucm                              false
% 3.20/1.01  --bmc1_add_unsat_core                   none
% 3.20/1.01  --bmc1_unsat_core_children              false
% 3.20/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.01  --bmc1_out_stat                         full
% 3.20/1.01  --bmc1_ground_init                      false
% 3.20/1.01  --bmc1_pre_inst_next_state              false
% 3.20/1.01  --bmc1_pre_inst_state                   false
% 3.20/1.01  --bmc1_pre_inst_reach_state             false
% 3.20/1.01  --bmc1_out_unsat_core                   false
% 3.20/1.01  --bmc1_aig_witness_out                  false
% 3.20/1.01  --bmc1_verbose                          false
% 3.20/1.01  --bmc1_dump_clauses_tptp                false
% 3.20/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.01  --bmc1_dump_file                        -
% 3.20/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.01  --bmc1_ucm_extend_mode                  1
% 3.20/1.01  --bmc1_ucm_init_mode                    2
% 3.20/1.01  --bmc1_ucm_cone_mode                    none
% 3.20/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.01  --bmc1_ucm_relax_model                  4
% 3.20/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.01  --bmc1_ucm_layered_model                none
% 3.20/1.01  --bmc1_ucm_max_lemma_size               10
% 3.20/1.01  
% 3.20/1.01  ------ AIG Options
% 3.20/1.01  
% 3.20/1.01  --aig_mode                              false
% 3.20/1.01  
% 3.20/1.01  ------ Instantiation Options
% 3.20/1.01  
% 3.20/1.01  --instantiation_flag                    true
% 3.20/1.01  --inst_sos_flag                         true
% 3.20/1.01  --inst_sos_phase                        true
% 3.20/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.01  --inst_lit_sel_side                     num_symb
% 3.20/1.01  --inst_solver_per_active                1400
% 3.20/1.01  --inst_solver_calls_frac                1.
% 3.20/1.01  --inst_passive_queue_type               priority_queues
% 3.20/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.01  --inst_passive_queues_freq              [25;2]
% 3.20/1.01  --inst_dismatching                      true
% 3.20/1.01  --inst_eager_unprocessed_to_passive     true
% 3.20/1.01  --inst_prop_sim_given                   true
% 3.20/1.01  --inst_prop_sim_new                     false
% 3.20/1.01  --inst_subs_new                         false
% 3.20/1.01  --inst_eq_res_simp                      false
% 3.20/1.01  --inst_subs_given                       false
% 3.20/1.01  --inst_orphan_elimination               true
% 3.20/1.01  --inst_learning_loop_flag               true
% 3.20/1.01  --inst_learning_start                   3000
% 3.20/1.01  --inst_learning_factor                  2
% 3.20/1.01  --inst_start_prop_sim_after_learn       3
% 3.20/1.01  --inst_sel_renew                        solver
% 3.20/1.01  --inst_lit_activity_flag                true
% 3.20/1.01  --inst_restr_to_given                   false
% 3.20/1.01  --inst_activity_threshold               500
% 3.20/1.01  --inst_out_proof                        true
% 3.20/1.01  
% 3.20/1.01  ------ Resolution Options
% 3.20/1.01  
% 3.20/1.01  --resolution_flag                       true
% 3.20/1.01  --res_lit_sel                           adaptive
% 3.20/1.01  --res_lit_sel_side                      none
% 3.20/1.01  --res_ordering                          kbo
% 3.20/1.01  --res_to_prop_solver                    active
% 3.20/1.01  --res_prop_simpl_new                    false
% 3.20/1.01  --res_prop_simpl_given                  true
% 3.20/1.01  --res_passive_queue_type                priority_queues
% 3.20/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.01  --res_passive_queues_freq               [15;5]
% 3.20/1.01  --res_forward_subs                      full
% 3.20/1.01  --res_backward_subs                     full
% 3.20/1.01  --res_forward_subs_resolution           true
% 3.20/1.01  --res_backward_subs_resolution          true
% 3.20/1.01  --res_orphan_elimination                true
% 3.20/1.01  --res_time_limit                        2.
% 3.20/1.01  --res_out_proof                         true
% 3.20/1.01  
% 3.20/1.01  ------ Superposition Options
% 3.20/1.01  
% 3.20/1.01  --superposition_flag                    true
% 3.20/1.01  --sup_passive_queue_type                priority_queues
% 3.20/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.01  --demod_completeness_check              fast
% 3.20/1.01  --demod_use_ground                      true
% 3.20/1.01  --sup_to_prop_solver                    passive
% 3.20/1.01  --sup_prop_simpl_new                    true
% 3.20/1.01  --sup_prop_simpl_given                  true
% 3.20/1.01  --sup_fun_splitting                     true
% 3.20/1.01  --sup_smt_interval                      50000
% 3.20/1.02  
% 3.20/1.02  ------ Superposition Simplification Setup
% 3.20/1.02  
% 3.20/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.20/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.20/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.20/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.20/1.02  --sup_immed_triv                        [TrivRules]
% 3.20/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_immed_bw_main                     []
% 3.20/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.20/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_input_bw                          []
% 3.20/1.02  
% 3.20/1.02  ------ Combination Options
% 3.20/1.02  
% 3.20/1.02  --comb_res_mult                         3
% 3.20/1.02  --comb_sup_mult                         2
% 3.20/1.02  --comb_inst_mult                        10
% 3.20/1.02  
% 3.20/1.02  ------ Debug Options
% 3.20/1.02  
% 3.20/1.02  --dbg_backtrace                         false
% 3.20/1.02  --dbg_dump_prop_clauses                 false
% 3.20/1.02  --dbg_dump_prop_clauses_file            -
% 3.20/1.02  --dbg_out_stat                          false
% 3.20/1.02  ------ Parsing...
% 3.20/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/1.02  ------ Proving...
% 3.20/1.02  ------ Problem Properties 
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  clauses                                 32
% 3.20/1.02  conjectures                             8
% 3.20/1.02  EPR                                     9
% 3.20/1.02  Horn                                    30
% 3.20/1.02  unary                                   3
% 3.20/1.02  binary                                  10
% 3.20/1.02  lits                                    86
% 3.20/1.02  lits eq                                 7
% 3.20/1.02  fd_pure                                 0
% 3.20/1.02  fd_pseudo                               0
% 3.20/1.02  fd_cond                                 0
% 3.20/1.02  fd_pseudo_cond                          1
% 3.20/1.02  AC symbols                              0
% 3.20/1.02  
% 3.20/1.02  ------ Schedule dynamic 5 is on 
% 3.20/1.02  
% 3.20/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  ------ 
% 3.20/1.02  Current options:
% 3.20/1.02  ------ 
% 3.20/1.02  
% 3.20/1.02  ------ Input Options
% 3.20/1.02  
% 3.20/1.02  --out_options                           all
% 3.20/1.02  --tptp_safe_out                         true
% 3.20/1.02  --problem_path                          ""
% 3.20/1.02  --include_path                          ""
% 3.20/1.02  --clausifier                            res/vclausify_rel
% 3.20/1.02  --clausifier_options                    ""
% 3.20/1.02  --stdin                                 false
% 3.20/1.02  --stats_out                             all
% 3.20/1.02  
% 3.20/1.02  ------ General Options
% 3.20/1.02  
% 3.20/1.02  --fof                                   false
% 3.20/1.02  --time_out_real                         305.
% 3.20/1.02  --time_out_virtual                      -1.
% 3.20/1.02  --symbol_type_check                     false
% 3.20/1.02  --clausify_out                          false
% 3.20/1.02  --sig_cnt_out                           false
% 3.20/1.02  --trig_cnt_out                          false
% 3.20/1.02  --trig_cnt_out_tolerance                1.
% 3.20/1.02  --trig_cnt_out_sk_spl                   false
% 3.20/1.02  --abstr_cl_out                          false
% 3.20/1.02  
% 3.20/1.02  ------ Global Options
% 3.20/1.02  
% 3.20/1.02  --schedule                              default
% 3.20/1.02  --add_important_lit                     false
% 3.20/1.02  --prop_solver_per_cl                    1000
% 3.20/1.02  --min_unsat_core                        false
% 3.20/1.02  --soft_assumptions                      false
% 3.20/1.02  --soft_lemma_size                       3
% 3.20/1.02  --prop_impl_unit_size                   0
% 3.20/1.02  --prop_impl_unit                        []
% 3.20/1.02  --share_sel_clauses                     true
% 3.20/1.02  --reset_solvers                         false
% 3.20/1.02  --bc_imp_inh                            [conj_cone]
% 3.20/1.02  --conj_cone_tolerance                   3.
% 3.20/1.02  --extra_neg_conj                        none
% 3.20/1.02  --large_theory_mode                     true
% 3.20/1.02  --prolific_symb_bound                   200
% 3.20/1.02  --lt_threshold                          2000
% 3.20/1.02  --clause_weak_htbl                      true
% 3.20/1.02  --gc_record_bc_elim                     false
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing Options
% 3.20/1.02  
% 3.20/1.02  --preprocessing_flag                    true
% 3.20/1.02  --time_out_prep_mult                    0.1
% 3.20/1.02  --splitting_mode                        input
% 3.20/1.02  --splitting_grd                         true
% 3.20/1.02  --splitting_cvd                         false
% 3.20/1.02  --splitting_cvd_svl                     false
% 3.20/1.02  --splitting_nvd                         32
% 3.20/1.02  --sub_typing                            true
% 3.20/1.02  --prep_gs_sim                           true
% 3.20/1.02  --prep_unflatten                        true
% 3.20/1.02  --prep_res_sim                          true
% 3.20/1.02  --prep_upred                            true
% 3.20/1.02  --prep_sem_filter                       exhaustive
% 3.20/1.02  --prep_sem_filter_out                   false
% 3.20/1.02  --pred_elim                             true
% 3.20/1.02  --res_sim_input                         true
% 3.20/1.02  --eq_ax_congr_red                       true
% 3.20/1.02  --pure_diseq_elim                       true
% 3.20/1.02  --brand_transform                       false
% 3.20/1.02  --non_eq_to_eq                          false
% 3.20/1.02  --prep_def_merge                        true
% 3.20/1.02  --prep_def_merge_prop_impl              false
% 3.20/1.02  --prep_def_merge_mbd                    true
% 3.20/1.02  --prep_def_merge_tr_red                 false
% 3.20/1.02  --prep_def_merge_tr_cl                  false
% 3.20/1.02  --smt_preprocessing                     true
% 3.20/1.02  --smt_ac_axioms                         fast
% 3.20/1.02  --preprocessed_out                      false
% 3.20/1.02  --preprocessed_stats                    false
% 3.20/1.02  
% 3.20/1.02  ------ Abstraction refinement Options
% 3.20/1.02  
% 3.20/1.02  --abstr_ref                             []
% 3.20/1.02  --abstr_ref_prep                        false
% 3.20/1.02  --abstr_ref_until_sat                   false
% 3.20/1.02  --abstr_ref_sig_restrict                funpre
% 3.20/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.02  --abstr_ref_under                       []
% 3.20/1.02  
% 3.20/1.02  ------ SAT Options
% 3.20/1.02  
% 3.20/1.02  --sat_mode                              false
% 3.20/1.02  --sat_fm_restart_options                ""
% 3.20/1.02  --sat_gr_def                            false
% 3.20/1.02  --sat_epr_types                         true
% 3.20/1.02  --sat_non_cyclic_types                  false
% 3.20/1.02  --sat_finite_models                     false
% 3.20/1.02  --sat_fm_lemmas                         false
% 3.20/1.02  --sat_fm_prep                           false
% 3.20/1.02  --sat_fm_uc_incr                        true
% 3.20/1.02  --sat_out_model                         small
% 3.20/1.02  --sat_out_clauses                       false
% 3.20/1.02  
% 3.20/1.02  ------ QBF Options
% 3.20/1.02  
% 3.20/1.02  --qbf_mode                              false
% 3.20/1.02  --qbf_elim_univ                         false
% 3.20/1.02  --qbf_dom_inst                          none
% 3.20/1.02  --qbf_dom_pre_inst                      false
% 3.20/1.02  --qbf_sk_in                             false
% 3.20/1.02  --qbf_pred_elim                         true
% 3.20/1.02  --qbf_split                             512
% 3.20/1.02  
% 3.20/1.02  ------ BMC1 Options
% 3.20/1.02  
% 3.20/1.02  --bmc1_incremental                      false
% 3.20/1.02  --bmc1_axioms                           reachable_all
% 3.20/1.02  --bmc1_min_bound                        0
% 3.20/1.02  --bmc1_max_bound                        -1
% 3.20/1.02  --bmc1_max_bound_default                -1
% 3.20/1.02  --bmc1_symbol_reachability              true
% 3.20/1.02  --bmc1_property_lemmas                  false
% 3.20/1.02  --bmc1_k_induction                      false
% 3.20/1.02  --bmc1_non_equiv_states                 false
% 3.20/1.02  --bmc1_deadlock                         false
% 3.20/1.02  --bmc1_ucm                              false
% 3.20/1.02  --bmc1_add_unsat_core                   none
% 3.20/1.02  --bmc1_unsat_core_children              false
% 3.20/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.02  --bmc1_out_stat                         full
% 3.20/1.02  --bmc1_ground_init                      false
% 3.20/1.02  --bmc1_pre_inst_next_state              false
% 3.20/1.02  --bmc1_pre_inst_state                   false
% 3.20/1.02  --bmc1_pre_inst_reach_state             false
% 3.20/1.02  --bmc1_out_unsat_core                   false
% 3.20/1.02  --bmc1_aig_witness_out                  false
% 3.20/1.02  --bmc1_verbose                          false
% 3.20/1.02  --bmc1_dump_clauses_tptp                false
% 3.20/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.02  --bmc1_dump_file                        -
% 3.20/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.02  --bmc1_ucm_extend_mode                  1
% 3.20/1.02  --bmc1_ucm_init_mode                    2
% 3.20/1.02  --bmc1_ucm_cone_mode                    none
% 3.20/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.02  --bmc1_ucm_relax_model                  4
% 3.20/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.02  --bmc1_ucm_layered_model                none
% 3.20/1.02  --bmc1_ucm_max_lemma_size               10
% 3.20/1.02  
% 3.20/1.02  ------ AIG Options
% 3.20/1.02  
% 3.20/1.02  --aig_mode                              false
% 3.20/1.02  
% 3.20/1.02  ------ Instantiation Options
% 3.20/1.02  
% 3.20/1.02  --instantiation_flag                    true
% 3.20/1.02  --inst_sos_flag                         true
% 3.20/1.02  --inst_sos_phase                        true
% 3.20/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.02  --inst_lit_sel_side                     none
% 3.20/1.02  --inst_solver_per_active                1400
% 3.20/1.02  --inst_solver_calls_frac                1.
% 3.20/1.02  --inst_passive_queue_type               priority_queues
% 3.20/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.02  --inst_passive_queues_freq              [25;2]
% 3.20/1.02  --inst_dismatching                      true
% 3.20/1.02  --inst_eager_unprocessed_to_passive     true
% 3.20/1.02  --inst_prop_sim_given                   true
% 3.20/1.02  --inst_prop_sim_new                     false
% 3.20/1.02  --inst_subs_new                         false
% 3.20/1.02  --inst_eq_res_simp                      false
% 3.20/1.02  --inst_subs_given                       false
% 3.20/1.02  --inst_orphan_elimination               true
% 3.20/1.02  --inst_learning_loop_flag               true
% 3.20/1.02  --inst_learning_start                   3000
% 3.20/1.02  --inst_learning_factor                  2
% 3.20/1.02  --inst_start_prop_sim_after_learn       3
% 3.20/1.02  --inst_sel_renew                        solver
% 3.20/1.02  --inst_lit_activity_flag                true
% 3.20/1.02  --inst_restr_to_given                   false
% 3.20/1.02  --inst_activity_threshold               500
% 3.20/1.02  --inst_out_proof                        true
% 3.20/1.02  
% 3.20/1.02  ------ Resolution Options
% 3.20/1.02  
% 3.20/1.02  --resolution_flag                       false
% 3.20/1.02  --res_lit_sel                           adaptive
% 3.20/1.02  --res_lit_sel_side                      none
% 3.20/1.02  --res_ordering                          kbo
% 3.20/1.02  --res_to_prop_solver                    active
% 3.20/1.02  --res_prop_simpl_new                    false
% 3.20/1.02  --res_prop_simpl_given                  true
% 3.20/1.02  --res_passive_queue_type                priority_queues
% 3.20/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.02  --res_passive_queues_freq               [15;5]
% 3.20/1.02  --res_forward_subs                      full
% 3.20/1.02  --res_backward_subs                     full
% 3.20/1.02  --res_forward_subs_resolution           true
% 3.20/1.02  --res_backward_subs_resolution          true
% 3.20/1.02  --res_orphan_elimination                true
% 3.20/1.02  --res_time_limit                        2.
% 3.20/1.02  --res_out_proof                         true
% 3.20/1.02  
% 3.20/1.02  ------ Superposition Options
% 3.20/1.02  
% 3.20/1.02  --superposition_flag                    true
% 3.20/1.02  --sup_passive_queue_type                priority_queues
% 3.20/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.02  --demod_completeness_check              fast
% 3.20/1.02  --demod_use_ground                      true
% 3.20/1.02  --sup_to_prop_solver                    passive
% 3.20/1.02  --sup_prop_simpl_new                    true
% 3.20/1.02  --sup_prop_simpl_given                  true
% 3.20/1.02  --sup_fun_splitting                     true
% 3.20/1.02  --sup_smt_interval                      50000
% 3.20/1.02  
% 3.20/1.02  ------ Superposition Simplification Setup
% 3.20/1.02  
% 3.20/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.20/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.20/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.20/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.20/1.02  --sup_immed_triv                        [TrivRules]
% 3.20/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_immed_bw_main                     []
% 3.20/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.20/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_input_bw                          []
% 3.20/1.02  
% 3.20/1.02  ------ Combination Options
% 3.20/1.02  
% 3.20/1.02  --comb_res_mult                         3
% 3.20/1.02  --comb_sup_mult                         2
% 3.20/1.02  --comb_inst_mult                        10
% 3.20/1.02  
% 3.20/1.02  ------ Debug Options
% 3.20/1.02  
% 3.20/1.02  --dbg_backtrace                         false
% 3.20/1.02  --dbg_dump_prop_clauses                 false
% 3.20/1.02  --dbg_dump_prop_clauses_file            -
% 3.20/1.02  --dbg_out_stat                          false
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  ------ Proving...
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  % SZS status Theorem for theBenchmark.p
% 3.20/1.02  
% 3.20/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/1.02  
% 3.20/1.02  fof(f1,axiom,(
% 3.20/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f30,plain,(
% 3.20/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/1.02    inference(nnf_transformation,[],[f1])).
% 3.20/1.02  
% 3.20/1.02  fof(f31,plain,(
% 3.20/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/1.02    inference(flattening,[],[f30])).
% 3.20/1.02  
% 3.20/1.02  fof(f40,plain,(
% 3.20/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.20/1.02    inference(cnf_transformation,[],[f31])).
% 3.20/1.02  
% 3.20/1.02  fof(f67,plain,(
% 3.20/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/1.02    inference(equality_resolution,[],[f40])).
% 3.20/1.02  
% 3.20/1.02  fof(f7,axiom,(
% 3.20/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f20,plain,(
% 3.20/1.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.20/1.02    inference(ennf_transformation,[],[f7])).
% 3.20/1.02  
% 3.20/1.02  fof(f21,plain,(
% 3.20/1.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(flattening,[],[f20])).
% 3.20/1.02  
% 3.20/1.02  fof(f51,plain,(
% 3.20/1.02    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f21])).
% 3.20/1.02  
% 3.20/1.02  fof(f11,conjecture,(
% 3.20/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f12,negated_conjecture,(
% 3.20/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.20/1.02    inference(negated_conjecture,[],[f11])).
% 3.20/1.02  
% 3.20/1.02  fof(f28,plain,(
% 3.20/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.20/1.02    inference(ennf_transformation,[],[f12])).
% 3.20/1.02  
% 3.20/1.02  fof(f29,plain,(
% 3.20/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/1.02    inference(flattening,[],[f28])).
% 3.20/1.02  
% 3.20/1.02  fof(f38,plain,(
% 3.20/1.02    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f37,plain,(
% 3.20/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f36,plain,(
% 3.20/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f35,plain,(
% 3.20/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f39,plain,(
% 3.20/1.02    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.20/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f38,f37,f36,f35])).
% 3.20/1.02  
% 3.20/1.02  fof(f56,plain,(
% 3.20/1.02    l1_pre_topc(sK0)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f4,axiom,(
% 3.20/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f17,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f4])).
% 3.20/1.02  
% 3.20/1.02  fof(f45,plain,(
% 3.20/1.02    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f17])).
% 3.20/1.02  
% 3.20/1.02  fof(f58,plain,(
% 3.20/1.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f9,axiom,(
% 3.20/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f24,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f9])).
% 3.20/1.02  
% 3.20/1.02  fof(f25,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(flattening,[],[f24])).
% 3.20/1.02  
% 3.20/1.02  fof(f53,plain,(
% 3.20/1.02    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f25])).
% 3.20/1.02  
% 3.20/1.02  fof(f2,axiom,(
% 3.20/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f13,plain,(
% 3.20/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.20/1.02    inference(ennf_transformation,[],[f2])).
% 3.20/1.02  
% 3.20/1.02  fof(f14,plain,(
% 3.20/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.20/1.02    inference(flattening,[],[f13])).
% 3.20/1.02  
% 3.20/1.02  fof(f43,plain,(
% 3.20/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f14])).
% 3.20/1.02  
% 3.20/1.02  fof(f60,plain,(
% 3.20/1.02    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f59,plain,(
% 3.20/1.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f10,axiom,(
% 3.20/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f26,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f10])).
% 3.20/1.02  
% 3.20/1.02  fof(f27,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(flattening,[],[f26])).
% 3.20/1.02  
% 3.20/1.02  fof(f54,plain,(
% 3.20/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f27])).
% 3.20/1.02  
% 3.20/1.02  fof(f57,plain,(
% 3.20/1.02    l1_pre_topc(sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f61,plain,(
% 3.20/1.02    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f62,plain,(
% 3.20/1.02    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f3,axiom,(
% 3.20/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f15,plain,(
% 3.20/1.02    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.20/1.02    inference(ennf_transformation,[],[f3])).
% 3.20/1.02  
% 3.20/1.02  fof(f16,plain,(
% 3.20/1.02    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(flattening,[],[f15])).
% 3.20/1.02  
% 3.20/1.02  fof(f44,plain,(
% 3.20/1.02    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f16])).
% 3.20/1.02  
% 3.20/1.02  fof(f6,axiom,(
% 3.20/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f19,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f6])).
% 3.20/1.02  
% 3.20/1.02  fof(f34,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(nnf_transformation,[],[f19])).
% 3.20/1.02  
% 3.20/1.02  fof(f50,plain,(
% 3.20/1.02    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f34])).
% 3.20/1.02  
% 3.20/1.02  fof(f42,plain,(
% 3.20/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f31])).
% 3.20/1.02  
% 3.20/1.02  fof(f5,axiom,(
% 3.20/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f18,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f5])).
% 3.20/1.02  
% 3.20/1.02  fof(f32,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(nnf_transformation,[],[f18])).
% 3.20/1.02  
% 3.20/1.02  fof(f33,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.02    inference(flattening,[],[f32])).
% 3.20/1.02  
% 3.20/1.02  fof(f46,plain,(
% 3.20/1.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f33])).
% 3.20/1.02  
% 3.20/1.02  fof(f49,plain,(
% 3.20/1.02    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f34])).
% 3.20/1.02  
% 3.20/1.02  fof(f8,axiom,(
% 3.20/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f22,plain,(
% 3.20/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.20/1.02    inference(ennf_transformation,[],[f8])).
% 3.20/1.02  
% 3.20/1.02  fof(f23,plain,(
% 3.20/1.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.20/1.02    inference(flattening,[],[f22])).
% 3.20/1.02  
% 3.20/1.02  fof(f52,plain,(
% 3.20/1.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f23])).
% 3.20/1.02  
% 3.20/1.02  fof(f55,plain,(
% 3.20/1.02    v2_pre_topc(sK0)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f48,plain,(
% 3.20/1.02    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f33])).
% 3.20/1.02  
% 3.20/1.02  fof(f65,plain,(
% 3.20/1.02    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f64,plain,(
% 3.20/1.02    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f63,plain,(
% 3.20/1.02    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2,plain,
% 3.20/1.02      ( r1_tarski(X0,X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4532,plain,
% 3.20/1.02      ( r1_tarski(sK2,sK2) ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_11,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ l1_pre_topc(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_24,negated_conjecture,
% 3.20/1.02      ( l1_pre_topc(sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_480,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | sK0 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_481,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_480]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1229,plain,
% 3.20/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.20/1.02      | ~ l1_pre_topc(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_570,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.20/1.02      | sK0 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_571,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_570]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1223,plain,
% 3.20/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2046,plain,
% 3.20/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_1229,c_1223]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_22,negated_conjecture,
% 3.20/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.20/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1243,plain,
% 3.20/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_13,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ r1_tarski(X0,X2)
% 3.20/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 3.20/1.02      | ~ l1_pre_topc(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_459,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ r1_tarski(X0,X2)
% 3.20/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 3.20/1.02      | sK0 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_460,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | ~ r1_tarski(X0,X1)
% 3.20/1.02      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_459]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1230,plain,
% 3.20/1.02      ( v3_pre_topc(X0,sK0) != iProver_top
% 3.20/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.20/1.02      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3643,plain,
% 3.20/1.02      ( v3_pre_topc(sK2,sK0) != iProver_top
% 3.20/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | r1_tarski(sK2,X0) != iProver_top
% 3.20/1.02      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_1243,c_1230]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3778,plain,
% 3.20/1.02      ( v3_pre_topc(sK2,sK0) != iProver_top
% 3.20/1.02      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
% 3.20/1.02      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_1243,c_3643]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3,plain,
% 3.20/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.20/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1251,plain,
% 3.20/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.20/1.02      | r1_tarski(X1,X2) != iProver_top
% 3.20/1.02      | r1_tarski(X0,X2) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3883,plain,
% 3.20/1.02      ( v3_pre_topc(sK2,sK0) != iProver_top
% 3.20/1.02      | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
% 3.20/1.02      | r1_tarski(sK2,X0) = iProver_top
% 3.20/1.02      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3778,c_1251]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4467,plain,
% 3.20/1.02      ( v3_pre_topc(sK2,sK0) != iProver_top
% 3.20/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top
% 3.20/1.02      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2046,c_3883]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4474,plain,
% 3.20/1.02      ( ~ v3_pre_topc(sK2,sK0)
% 3.20/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
% 3.20/1.02      | ~ r1_tarski(sK2,sK2) ),
% 3.20/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4467]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_20,negated_conjecture,
% 3.20/1.02      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1245,plain,
% 3.20/1.02      ( v3_pre_topc(sK3,sK1) = iProver_top
% 3.20/1.02      | v6_tops_1(sK2,sK0) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_21,negated_conjecture,
% 3.20/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.20/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1244,plain,
% 3.20/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_14,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ l1_pre_topc(X1)
% 3.20/1.02      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_23,negated_conjecture,
% 3.20/1.02      ( l1_pre_topc(sK1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_294,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_295,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,sK1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_294]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1241,plain,
% 3.20/1.02      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 3.20/1.02      | v3_pre_topc(X0,sK1) != iProver_top
% 3.20/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3298,plain,
% 3.20/1.02      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 3.20/1.02      | v3_pre_topc(sK3,sK1) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_1244,c_1241]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3585,plain,
% 3.20/1.02      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 3.20/1.02      | v6_tops_1(sK2,sK0) = iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_1245,c_3298]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_30,plain,
% 3.20/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_31,plain,
% 3.20/1.02      ( v3_pre_topc(sK3,sK1) = iProver_top
% 3.20/1.02      | v6_tops_1(sK2,sK0) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_19,negated_conjecture,
% 3.20/1.02      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_32,plain,
% 3.20/1.02      ( v6_tops_1(sK2,sK0) = iProver_top
% 3.20/1.02      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_18,negated_conjecture,
% 3.20/1.02      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_33,plain,
% 3.20/1.02      ( v6_tops_1(sK3,sK1) != iProver_top
% 3.20/1.02      | v6_tops_1(sK2,sK0) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ l1_pre_topc(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_432,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_433,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_432]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1340,plain,
% 3.20/1.02      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_433]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1341,plain,
% 3.20/1.02      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.20/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1340]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_420,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_421,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_420]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1352,plain,
% 3.20/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_421]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1353,plain,
% 3.20/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.20/1.02      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1352]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_9,plain,
% 3.20/1.02      ( v6_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ l1_pre_topc(X1)
% 3.20/1.02      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 3.20/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_357,plain,
% 3.20/1.02      ( v6_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_358,plain,
% 3.20/1.02      ( v6_tops_1(X0,sK1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_357]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1370,plain,
% 3.20/1.02      ( v6_tops_1(sK3,sK1)
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_358]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1371,plain,
% 3.20/1.02      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
% 3.20/1.02      | v6_tops_1(sK3,sK1) = iProver_top
% 3.20/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1370]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_0,plain,
% 3.20/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.20/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1497,plain,
% 3.20/1.02      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
% 3.20/1.02      | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 3.20/1.02      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1498,plain,
% 3.20/1.02      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 3.20/1.02      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
% 3.20/1.02      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1497]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_8,plain,
% 3.20/1.02      ( ~ v4_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.20/1.02      | ~ l1_pre_topc(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_372,plain,
% 3.20/1.02      ( ~ v4_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_373,plain,
% 3.20/1.02      ( ~ v4_tops_1(X0,sK1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_372]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1507,plain,
% 3.20/1.02      ( ~ v4_tops_1(sK3,sK1)
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_373]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1508,plain,
% 3.20/1.02      ( v4_tops_1(sK3,sK1) != iProver_top
% 3.20/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.20/1.02      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1507]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_309,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ r1_tarski(X0,X2)
% 3.20/1.02      | r1_tarski(X0,k1_tops_1(X1,X2))
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_310,plain,
% 3.20/1.02      ( ~ v3_pre_topc(X0,sK1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | ~ r1_tarski(X0,X1)
% 3.20/1.02      | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_309]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1512,plain,
% 3.20/1.02      ( ~ v3_pre_topc(sK3,sK1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | ~ r1_tarski(sK3,X0)
% 3.20/1.02      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_310]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3623,plain,
% 3.20/1.02      ( ~ v3_pre_topc(sK3,sK1)
% 3.20/1.02      | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.20/1.02      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 3.20/1.02      | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_1512]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3624,plain,
% 3.20/1.02      ( v3_pre_topc(sK3,sK1) != iProver_top
% 3.20/1.02      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.20/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.20/1.02      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
% 3.20/1.02      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_3623]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3772,plain,
% 3.20/1.02      ( v6_tops_1(sK2,sK0) = iProver_top ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_3585,c_30,c_31,c_32,c_33,c_1341,c_1353,c_1371,c_1498,
% 3.20/1.02                 c_1508,c_3624]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_10,plain,
% 3.20/1.02      ( ~ v6_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ l1_pre_topc(X1)
% 3.20/1.02      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 3.20/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_492,plain,
% 3.20/1.02      ( ~ v6_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
% 3.20/1.02      | sK0 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_493,plain,
% 3.20/1.02      ( ~ v6_tops_1(X0,sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_492]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1228,plain,
% 3.20/1.02      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
% 3.20/1.02      | v6_tops_1(X0,sK0) != iProver_top
% 3.20/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2517,plain,
% 3.20/1.02      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 3.20/1.02      | v6_tops_1(sK2,sK0) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_1243,c_1228]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3776,plain,
% 3.20/1.02      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3772,c_2517]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_582,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | sK0 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_583,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_582]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1222,plain,
% 3.20/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_12,plain,
% 3.20/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.20/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.20/1.02      | ~ v2_pre_topc(X0)
% 3.20/1.02      | ~ l1_pre_topc(X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_25,negated_conjecture,
% 3.20/1.02      ( v2_pre_topc(sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_273,plain,
% 3.20/1.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.20/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.20/1.02      | ~ l1_pre_topc(X0)
% 3.20/1.02      | sK0 != X0 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_274,plain,
% 3.20/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | ~ l1_pre_topc(sK0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_273]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_278,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_274,c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_279,plain,
% 3.20/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_278]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1242,plain,
% 3.20/1.02      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 3.20/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1947,plain,
% 3.20/1.02      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
% 3.20/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_1222,c_1242]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4186,plain,
% 3.20/1.02      ( v3_pre_topc(sK2,sK0) = iProver_top
% 3.20/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3776,c_1947]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4187,plain,
% 3.20/1.02      ( v3_pre_topc(sK2,sK0)
% 3.20/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.20/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4186]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_6,plain,
% 3.20/1.02      ( v4_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.20/1.02      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.20/1.02      | ~ l1_pre_topc(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_552,plain,
% 3.20/1.02      ( v4_tops_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.20/1.02      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.20/1.02      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.20/1.02      | sK0 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_553,plain,
% 3.20/1.02      ( v4_tops_1(X0,sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 3.20/1.02      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_552]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1224,plain,
% 3.20/1.02      ( v4_tops_1(X0,sK0) = iProver_top
% 3.20/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 3.20/1.02      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4183,plain,
% 3.20/1.02      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.20/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.20/1.02      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 3.20/1.02      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3776,c_1224]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4184,plain,
% 3.20/1.02      ( v4_tops_1(sK2,sK0)
% 3.20/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.20/1.02      | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
% 3.20/1.02      | ~ r1_tarski(sK2,sK2) ),
% 3.20/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4183]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_15,negated_conjecture,
% 3.20/1.02      ( ~ v3_pre_topc(sK2,sK0)
% 3.20/1.02      | ~ v6_tops_1(sK3,sK1)
% 3.20/1.02      | ~ v4_tops_1(sK2,sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_16,negated_conjecture,
% 3.20/1.02      ( ~ v3_pre_topc(sK2,sK0)
% 3.20/1.02      | v4_tops_1(sK3,sK1)
% 3.20/1.02      | ~ v4_tops_1(sK2,sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_17,negated_conjecture,
% 3.20/1.02      ( v3_pre_topc(sK3,sK1)
% 3.20/1.02      | ~ v3_pre_topc(sK2,sK0)
% 3.20/1.02      | ~ v4_tops_1(sK2,sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(contradiction,plain,
% 3.20/1.02      ( $false ),
% 3.20/1.02      inference(minisat,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_4532,c_4474,c_4187,c_4184,c_3623,c_1507,c_1497,c_1370,
% 3.20/1.02                 c_1352,c_1340,c_15,c_16,c_17,c_21,c_22]) ).
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.02  
% 3.20/1.02  ------                               Statistics
% 3.20/1.02  
% 3.20/1.02  ------ General
% 3.20/1.02  
% 3.20/1.02  abstr_ref_over_cycles:                  0
% 3.20/1.02  abstr_ref_under_cycles:                 0
% 3.20/1.02  gc_basic_clause_elim:                   0
% 3.20/1.02  forced_gc_time:                         0
% 3.20/1.02  parsing_time:                           0.009
% 3.20/1.02  unif_index_cands_time:                  0.
% 3.20/1.02  unif_index_add_time:                    0.
% 3.20/1.02  orderings_time:                         0.
% 3.20/1.02  out_proof_time:                         0.013
% 3.20/1.02  total_time:                             0.183
% 3.20/1.02  num_of_symbols:                         46
% 3.20/1.02  num_of_terms:                           5448
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing
% 3.20/1.02  
% 3.20/1.02  num_of_splits:                          0
% 3.20/1.02  num_of_split_atoms:                     0
% 3.20/1.02  num_of_reused_defs:                     0
% 3.20/1.02  num_eq_ax_congr_red:                    2
% 3.20/1.02  num_of_sem_filtered_clauses:            1
% 3.20/1.02  num_of_subtypes:                        0
% 3.20/1.02  monotx_restored_types:                  0
% 3.20/1.02  sat_num_of_epr_types:                   0
% 3.20/1.02  sat_num_of_non_cyclic_types:            0
% 3.20/1.02  sat_guarded_non_collapsed_types:        0
% 3.20/1.02  num_pure_diseq_elim:                    0
% 3.20/1.02  simp_replaced_by:                       0
% 3.20/1.02  res_preprocessed:                       112
% 3.20/1.02  prep_upred:                             0
% 3.20/1.02  prep_unflattend:                        21
% 3.20/1.02  smt_new_axioms:                         0
% 3.20/1.02  pred_elim_cands:                        7
% 3.20/1.02  pred_elim:                              2
% 3.20/1.02  pred_elim_cl:                           -7
% 3.20/1.02  pred_elim_cycles:                       3
% 3.20/1.02  merged_defs:                            0
% 3.20/1.02  merged_defs_ncl:                        0
% 3.20/1.02  bin_hyper_res:                          0
% 3.20/1.02  prep_cycles:                            3
% 3.20/1.02  pred_elim_time:                         0.007
% 3.20/1.02  splitting_time:                         0.
% 3.20/1.02  sem_filter_time:                        0.
% 3.20/1.02  monotx_time:                            0.001
% 3.20/1.02  subtype_inf_time:                       0.
% 3.20/1.02  
% 3.20/1.02  ------ Problem properties
% 3.20/1.02  
% 3.20/1.02  clauses:                                32
% 3.20/1.02  conjectures:                            8
% 3.20/1.02  epr:                                    9
% 3.20/1.02  horn:                                   30
% 3.20/1.02  ground:                                 8
% 3.20/1.02  unary:                                  3
% 3.20/1.02  binary:                                 10
% 3.20/1.02  lits:                                   86
% 3.20/1.02  lits_eq:                                7
% 3.20/1.02  fd_pure:                                0
% 3.20/1.02  fd_pseudo:                              0
% 3.20/1.02  fd_cond:                                0
% 3.20/1.02  fd_pseudo_cond:                         1
% 3.20/1.02  ac_symbols:                             0
% 3.20/1.02  
% 3.20/1.02  ------ Propositional Solver
% 3.20/1.02  
% 3.20/1.02  prop_solver_calls:                      22
% 3.20/1.02  prop_fast_solver_calls:                 837
% 3.20/1.02  smt_solver_calls:                       0
% 3.20/1.02  smt_fast_solver_calls:                  0
% 3.20/1.02  prop_num_of_clauses:                    2112
% 3.20/1.02  prop_preprocess_simplified:             6166
% 3.20/1.02  prop_fo_subsumed:                       2
% 3.20/1.02  prop_solver_time:                       0.
% 3.20/1.02  smt_solver_time:                        0.
% 3.20/1.02  smt_fast_solver_time:                   0.
% 3.20/1.02  prop_fast_solver_time:                  0.
% 3.20/1.02  prop_unsat_core_time:                   0.
% 3.20/1.02  
% 3.20/1.02  ------ QBF
% 3.20/1.02  
% 3.20/1.02  qbf_q_res:                              0
% 3.20/1.02  qbf_num_tautologies:                    0
% 3.20/1.02  qbf_prep_cycles:                        0
% 3.20/1.02  
% 3.20/1.02  ------ BMC1
% 3.20/1.02  
% 3.20/1.02  bmc1_current_bound:                     -1
% 3.20/1.02  bmc1_last_solved_bound:                 -1
% 3.20/1.02  bmc1_unsat_core_size:                   -1
% 3.20/1.02  bmc1_unsat_core_parents_size:           -1
% 3.20/1.02  bmc1_merge_next_fun:                    0
% 3.20/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.02  
% 3.20/1.02  ------ Instantiation
% 3.20/1.02  
% 3.20/1.02  inst_num_of_clauses:                    758
% 3.20/1.02  inst_num_in_passive:                    239
% 3.20/1.02  inst_num_in_active:                     274
% 3.20/1.02  inst_num_in_unprocessed:                244
% 3.20/1.02  inst_num_of_loops:                      297
% 3.20/1.02  inst_num_of_learning_restarts:          0
% 3.20/1.02  inst_num_moves_active_passive:          21
% 3.20/1.02  inst_lit_activity:                      0
% 3.20/1.02  inst_lit_activity_moves:                0
% 3.20/1.02  inst_num_tautologies:                   0
% 3.20/1.02  inst_num_prop_implied:                  0
% 3.20/1.02  inst_num_existing_simplified:           0
% 3.20/1.02  inst_num_eq_res_simplified:             0
% 3.20/1.02  inst_num_child_elim:                    0
% 3.20/1.02  inst_num_of_dismatching_blockings:      22
% 3.20/1.02  inst_num_of_non_proper_insts:           450
% 3.20/1.02  inst_num_of_duplicates:                 0
% 3.20/1.02  inst_inst_num_from_inst_to_res:         0
% 3.20/1.02  inst_dismatching_checking_time:         0.
% 3.20/1.02  
% 3.20/1.02  ------ Resolution
% 3.20/1.02  
% 3.20/1.02  res_num_of_clauses:                     0
% 3.20/1.02  res_num_in_passive:                     0
% 3.20/1.02  res_num_in_active:                      0
% 3.20/1.02  res_num_of_loops:                       115
% 3.20/1.02  res_forward_subset_subsumed:            15
% 3.20/1.02  res_backward_subset_subsumed:           0
% 3.20/1.02  res_forward_subsumed:                   0
% 3.20/1.02  res_backward_subsumed:                  0
% 3.20/1.02  res_forward_subsumption_resolution:     0
% 3.20/1.02  res_backward_subsumption_resolution:    0
% 3.20/1.02  res_clause_to_clause_subsumption:       336
% 3.20/1.02  res_orphan_elimination:                 0
% 3.20/1.02  res_tautology_del:                      11
% 3.20/1.02  res_num_eq_res_simplified:              0
% 3.20/1.02  res_num_sel_changes:                    0
% 3.20/1.02  res_moves_from_active_to_pass:          0
% 3.20/1.02  
% 3.20/1.02  ------ Superposition
% 3.20/1.02  
% 3.20/1.02  sup_time_total:                         0.
% 3.20/1.02  sup_time_generating:                    0.
% 3.20/1.02  sup_time_sim_full:                      0.
% 3.20/1.02  sup_time_sim_immed:                     0.
% 3.20/1.02  
% 3.20/1.02  sup_num_of_clauses:                     104
% 3.20/1.02  sup_num_in_active:                      52
% 3.20/1.02  sup_num_in_passive:                     52
% 3.20/1.02  sup_num_of_loops:                       58
% 3.20/1.02  sup_fw_superposition:                   45
% 3.20/1.02  sup_bw_superposition:                   47
% 3.20/1.02  sup_immediate_simplified:               6
% 3.20/1.02  sup_given_eliminated:                   0
% 3.20/1.02  comparisons_done:                       0
% 3.20/1.02  comparisons_avoided:                    0
% 3.20/1.02  
% 3.20/1.02  ------ Simplifications
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  sim_fw_subset_subsumed:                 4
% 3.20/1.02  sim_bw_subset_subsumed:                 3
% 3.20/1.02  sim_fw_subsumed:                        2
% 3.20/1.02  sim_bw_subsumed:                        2
% 3.20/1.02  sim_fw_subsumption_res:                 0
% 3.20/1.02  sim_bw_subsumption_res:                 0
% 3.20/1.02  sim_tautology_del:                      5
% 3.20/1.02  sim_eq_tautology_del:                   2
% 3.20/1.02  sim_eq_res_simp:                        0
% 3.20/1.02  sim_fw_demodulated:                     0
% 3.20/1.02  sim_bw_demodulated:                     1
% 3.20/1.02  sim_light_normalised:                   0
% 3.20/1.02  sim_joinable_taut:                      0
% 3.20/1.02  sim_joinable_simp:                      0
% 3.20/1.02  sim_ac_normalised:                      0
% 3.20/1.02  sim_smt_subsumption:                    0
% 3.20/1.02  
%------------------------------------------------------------------------------
