%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1377+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:35 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  232 (17323 expanded)
%              Number of clauses        :  178 (6612 expanded)
%              Number of leaves         :   14 (3312 expanded)
%              Depth                    :   38
%              Number of atoms          : 1145 (85803 expanded)
%              Number of equality atoms :  605 (12279 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
     => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v2_compts_1(sK3,X0) )
        & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(sK3,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v2_compts_1(X1,sK2) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
              & v2_compts_1(X1,sK2) ) ) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_compts_1(sK3,sK2) )
    & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
      | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        & v2_compts_1(sK3,sK2) ) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( v1_finset_1(X3)
                      & m1_setfam_1(X3,X1)
                      & r1_tarski(X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X2,X0)
                  | ~ m1_setfam_1(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( v1_finset_1(X5)
                      & m1_setfam_1(X5,X1)
                      & r1_tarski(X5,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( v1_finset_1(X5)
          & m1_setfam_1(X5,X1)
          & r1_tarski(X5,X4)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK1(X0,X1,X4))
        & m1_setfam_1(sK1(X0,X1,X4),X1)
        & r1_tarski(sK1(X0,X1,X4),X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X1)
              | ~ r1_tarski(X3,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X2,X0)
          & m1_setfam_1(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X3] :
            ( ~ v1_finset_1(X3)
            | ~ m1_setfam_1(X3,X1)
            | ~ r1_tarski(X3,sK0(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK0(X0,X1),X0)
        & m1_setfam_1(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ( ! [X3] :
                    ( ~ v1_finset_1(X3)
                    | ~ m1_setfam_1(X3,X1)
                    | ~ r1_tarski(X3,sK0(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & v1_tops_2(sK0(X0,X1),X0)
                & m1_setfam_1(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ( v1_finset_1(sK1(X0,X1,X4))
                    & m1_setfam_1(sK1(X0,X1,X4),X1)
                    & r1_tarski(sK1(X0,X1,X4),X4)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | m1_setfam_1(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( m1_setfam_1(sK1(X0,X1,X4),X1)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | v1_tops_2(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X4),X4)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v1_finset_1(X3)
      | ~ m1_setfam_1(X3,X1)
      | ~ r1_tarski(X3,sK0(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( v1_finset_1(sK1(X0,X1,X4))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2168,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2176,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2620,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_2178])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2187,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3891,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2620,c_2187])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2611,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_2177])).

cnf(c_4106,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3891,c_2611])).

cnf(c_4107,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4106])).

cnf(c_4112,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(superposition,[status(thm)],[c_2168,c_4107])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2174,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4127,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4112,c_2174])).

cnf(c_4597,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4127])).

cnf(c_51,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2297,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2613,plain,
    ( ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2611])).

cnf(c_2615,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_2613])).

cnf(c_3125,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X1) != g1_pre_topc(u1_struct_0(sK2),X0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3079,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2697])).

cnf(c_3310,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3079])).

cnf(c_4658,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4597,c_23,c_51,c_2297,c_2615,c_3125,c_3310])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_setfam_1(sK0(X1,X0),X0)
    | v2_compts_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2184,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_setfam_1(sK0(X1,X0),X0) = iProver_top
    | v2_compts_1(X0,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4741,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X0) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2184])).

cnf(c_28,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_50,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_52,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_2298,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2297])).

cnf(c_4935,plain,
    ( v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4741,c_28,c_52,c_2298])).

cnf(c_4936,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X0) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4935])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_compts_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | v2_compts_1(X0,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_455,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_456,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_460,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_25,c_23])).

cnf(c_2164,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_3036,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_2164])).

cnf(c_3112,plain,
    ( v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3036,c_28,c_52,c_2298])).

cnf(c_3113,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3112])).

cnf(c_4674,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4658,c_3113])).

cnf(c_4740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2183])).

cnf(c_4742,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4740,c_4658])).

cnf(c_6153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4674,c_28,c_52,c_2298,c_4742])).

cnf(c_22,negated_conjecture,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2169,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_392,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_393,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_25,c_23])).

cnf(c_2167,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_8,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X0,X2)
    | ~ v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2179,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | m1_setfam_1(X0,X2) != iProver_top
    | v2_compts_1(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3199,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_tops_2(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2179,c_2164])).

cnf(c_3822,plain,
    ( v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | v1_tops_2(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3199,c_28,c_52,c_2298])).

cnf(c_3823,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_tops_2(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3822])).

cnf(c_4667,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_tops_2(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4658,c_3823])).

cnf(c_4739,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2179])).

cnf(c_4743,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4739,c_4658])).

cnf(c_5732,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4667,c_28,c_52,c_2298,c_4743])).

cnf(c_5742,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5732,c_2178])).

cnf(c_6961,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))))
    | v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(X1,X0) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5742,c_4107])).

cnf(c_15286,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0,X1))))
    | v1_tops_2(X1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(X1,X0) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_6961])).

cnf(c_15481,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))))
    | v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(X0,sK3) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_15286])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2172,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4681,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4658,c_2172])).

cnf(c_6,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_setfam_1(X0,X2)
    | m1_setfam_1(sK1(X1,X2,X0),X2)
    | ~ v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2181,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_setfam_1(X0,X2) != iProver_top
    | m1_setfam_1(sK1(X1,X2,X0),X2) = iProver_top
    | v2_compts_1(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6159,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6153,c_2181])).

cnf(c_2,plain,
    ( v1_tops_2(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_compts_1(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2185,plain,
    ( v1_tops_2(sK0(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_compts_1(X1,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4731,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2185])).

cnf(c_5136,plain,
    ( v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4731,c_28,c_52,c_2298])).

cnf(c_5137,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5136])).

cnf(c_15,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_434,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_435,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_439,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_25,c_23])).

cnf(c_2165,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_tops_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_4678,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_tops_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4658,c_2165])).

cnf(c_5142,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5137,c_4678])).

cnf(c_8420,plain,
    ( v2_compts_1(X1,sK2) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6159,c_28,c_52,c_2298,c_4742,c_5142])).

cnf(c_8421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8420])).

cnf(c_7,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_setfam_1(X0,X2)
    | ~ v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2180,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK1(X1,X2,X0),X0) = iProver_top
    | m1_setfam_1(X0,X2) != iProver_top
    | v2_compts_1(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6160,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6153,c_2180])).

cnf(c_6141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5142,c_28,c_52,c_2298,c_4742])).

cnf(c_6142,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6141])).

cnf(c_9285,plain,
    ( v2_compts_1(X1,sK2) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | r1_tarski(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6160,c_28,c_6142])).

cnf(c_9286,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9285])).

cnf(c_16,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_413,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_414,plain,
    ( ~ v1_tops_2(X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_418,plain,
    ( ~ v1_tops_2(X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_25,c_23])).

cnf(c_2166,plain,
    ( v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,sK0(X1,X2))
    | ~ m1_setfam_1(X0,X2)
    | v2_compts_1(X2,X1)
    | ~ v1_finset_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,sK0(X1,X2)) != iProver_top
    | m1_setfam_1(X0,X2) != iProver_top
    | v2_compts_1(X2,X1) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3345,plain,
    ( v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | r1_tarski(X0,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_2186])).

cnf(c_3493,plain,
    ( v1_finset_1(X0) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | r1_tarski(X0,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v1_tops_2(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3345,c_28,c_52,c_2298])).

cnf(c_3494,plain,
    ( v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | r1_tarski(X0,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3493])).

cnf(c_4672,plain,
    ( v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4658,c_3494])).

cnf(c_4738,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | r1_tarski(X0,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2186])).

cnf(c_4744,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_finset_1(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4738,c_4658])).

cnf(c_5541,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4672,c_28,c_52,c_2298,c_4744])).

cnf(c_9291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X0) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top
    | v1_finset_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9286,c_5541])).

cnf(c_5,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_setfam_1(X0,X2)
    | ~ v2_compts_1(X2,X1)
    | v1_finset_1(sK1(X1,X2,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2182,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_setfam_1(X0,X2) != iProver_top
    | v2_compts_1(X2,X1) != iProver_top
    | v1_finset_1(sK1(X1,X2,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6161,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top
    | v1_finset_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6153,c_2182])).

cnf(c_9421,plain,
    ( v2_compts_1(X1,sK2) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X0) != iProver_top
    | m1_subset_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9291,c_28,c_6142,c_6161])).

cnf(c_9422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X0) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9421])).

cnf(c_9427,plain,
    ( v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X0) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2179,c_9422])).

cnf(c_11580,plain,
    ( v2_compts_1(X1,sK2) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9427,c_28,c_6142,c_6153])).

cnf(c_11581,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK1(sK2,X1,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X0) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X1) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_11580])).

cnf(c_11586,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),X0) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8421,c_11581])).

cnf(c_11930,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11586,c_4936])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2173,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4683,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4658,c_2173])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1704,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2395,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_1716,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2259,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_2319,plain,
    ( ~ m1_subset_1(sK3,X0)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_2507,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2319])).

cnf(c_2508,plain,
    ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2507])).

cnf(c_1715,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2640,plain,
    ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1715])).

cnf(c_4807,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4683,c_23,c_33,c_51,c_2297,c_2395,c_2508,c_2615,c_2640,c_3125,c_3310,c_4681])).

cnf(c_11936,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11930,c_4807])).

cnf(c_15498,plain,
    ( m1_setfam_1(X0,sK3) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))))
    | v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15481,c_4681,c_11936])).

cnf(c_15499,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,X0))))
    | v1_tops_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_setfam_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_15498])).

cnf(c_15508,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))))
    | v1_tops_2(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK3) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6153,c_15499])).

cnf(c_16177,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK3) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15508,c_28,c_52,c_2298,c_4742,c_5142])).

cnf(c_16183,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3,sK0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4936,c_16177])).

cnf(c_29,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17194,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16183,c_29,c_4681,c_11936])).

cnf(c_4735,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X1) = iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2181])).

cnf(c_4747,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X1) = iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4735,c_4658])).

cnf(c_7402,plain,
    ( v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X1) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4747,c_28,c_52,c_2298])).

cnf(c_7403,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X1) = iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7402])).

cnf(c_4736,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X0) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2180])).

cnf(c_4746,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X0) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4736,c_4658])).

cnf(c_7280,plain,
    ( v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4746,c_28,c_52,c_2298])).

cnf(c_7281,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X0) = iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7280])).

cnf(c_5741,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),sK0(sK2,X2)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X2) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X2,sK2) = iProver_top
    | v1_finset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5732,c_2186])).

cnf(c_4737,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_finset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_2182])).

cnf(c_4745,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_finset_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4737,c_4658])).

cnf(c_8185,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),sK0(sK2,X2)) != iProver_top
    | m1_setfam_1(X0,X1) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,X0),X2) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5741,c_28,c_52,c_2298,c_4745])).

cnf(c_8191,plain,
    ( v1_tops_2(sK0(sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,sK0(sK2,X0)),X0) != iProver_top
    | m1_setfam_1(sK0(sK2,X0),X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7281,c_8185])).

cnf(c_837,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_compts_1(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_838,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v2_compts_1(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_837])).

cnf(c_839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_17357,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tops_2(sK0(sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,sK0(sK2,X0)),X0) != iProver_top
    | m1_setfam_1(sK0(sK2,X0),X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8191,c_839])).

cnf(c_17358,plain,
    ( v1_tops_2(sK0(sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1,sK0(sK2,X0)),X0) != iProver_top
    | m1_setfam_1(sK0(sK2,X0),X1) != iProver_top
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_17357])).

cnf(c_17363,plain,
    ( v1_tops_2(sK0(sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_setfam_1(sK0(sK2,X0),X0) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7403,c_17358])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_setfam_1(sK0(X1,X0),X0)
    | v2_compts_1(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_setfam_1(sK0(sK2,X0),X0)
    | v2_compts_1(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_854,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_setfam_1(sK0(sK2,X0),X0) = iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_23460,plain,
    ( v1_tops_2(sK0(sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17363,c_839,c_854])).

cnf(c_23466,plain,
    ( v1_tops_2(sK0(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_23460])).

cnf(c_545,plain,
    ( v1_tops_2(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_compts_1(X1,X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_546,plain,
    ( v1_tops_2(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_compts_1(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_547,plain,
    ( v1_tops_2(sK0(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_24051,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23466,c_547,c_839])).

cnf(c_24057,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17194,c_24051])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24057,c_11936,c_4681])).


%------------------------------------------------------------------------------
