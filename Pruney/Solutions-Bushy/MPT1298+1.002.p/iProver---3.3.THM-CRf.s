%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1298+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:22 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 999 expanded)
%              Number of clauses        :  102 ( 315 expanded)
%              Number of leaves         :   14 ( 207 expanded)
%              Depth                    :   22
%              Number of atoms          :  673 (5076 expanded)
%              Number of equality atoms :  146 ( 351 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v2_tops_2(X1,X0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v2_tops_2(X1,X0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v2_tops_2(X1,X0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),sK4),X0)
          | ~ v2_tops_2(sK4,X0) )
        & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),sK4),X0)
          | v2_tops_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | v2_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),X1),sK3)
            | ~ v2_tops_2(X1,sK3) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(sK3),X1),sK3)
            | v2_tops_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
      | ~ v2_tops_2(sK4,sK3) )
    & ( v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
      | v2_tops_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f41,f40])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK1(X0,X1),X0)
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | r2_hidden(sK2(X0,X1,X2),X2) )
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
    | v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
    | ~ v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2013,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2648,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_5,plain,
    ( v2_tops_2(X0,X1)
    | r2_hidden(sK1(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_408,plain,
    ( v2_tops_2(X0,X1)
    | r2_hidden(sK1(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_409,plain,
    ( v2_tops_2(X0,sK3)
    | r2_hidden(sK1(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_2008,plain,
    ( v2_tops_2(X0_44,sK3)
    | r2_hidden(sK1(sK3,X0_44),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_2653,plain,
    ( v2_tops_2(X0_44,sK3) = iProver_top
    | r2_hidden(sK1(sK3,X0_44),X0_44) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_3488,plain,
    ( v2_tops_2(sK4,sK3) = iProver_top
    | r2_hidden(sK1(sK3,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_2653])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2017,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X0_45)))
    | k7_setfam_1(X0_45,k7_setfam_1(X0_45,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2644,plain,
    ( k7_setfam_1(X0_45,k7_setfam_1(X0_45,X0_44)) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_3078,plain,
    ( k7_setfam_1(u1_struct_0(sK3),k7_setfam_1(u1_struct_0(sK3),sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_2648,c_2644])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2018,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X0_45)))
    | m1_subset_1(k7_setfam_1(X0_45,X0_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2643,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_45,X0_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2018])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2019,plain,
    ( ~ r2_hidden(X0_44,k7_setfam_1(X0_45,X1_44))
    | r2_hidden(k3_subset_1(X0_45,X0_44),X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_45)))
    | ~ m1_subset_1(k7_setfam_1(X0_45,X1_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2642,plain,
    ( r2_hidden(X0_44,k7_setfam_1(X0_45,X1_44)) != iProver_top
    | r2_hidden(k3_subset_1(X0_45,X0_44),X1_44) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_45,X1_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2016,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | m1_subset_1(X0_44,X0_45)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2645,plain,
    ( r2_hidden(X0_44,X1_44) != iProver_top
    | m1_subset_1(X0_44,X0_45) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_2794,plain,
    ( r2_hidden(X0_44,k7_setfam_1(X0_45,X1_44)) != iProver_top
    | r2_hidden(k3_subset_1(X0_45,X0_44),X1_44) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2642,c_2643,c_2645])).

cnf(c_4607,plain,
    ( r2_hidden(X0_44,k7_setfam_1(X0_45,k7_setfam_1(X0_45,X1_44))) != iProver_top
    | r2_hidden(k3_subset_1(X0_45,X0_44),k7_setfam_1(X0_45,X1_44)) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2643,c_2794])).

cnf(c_6073,plain,
    ( r2_hidden(X0_44,sK4) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),X0_44),k7_setfam_1(u1_struct_0(sK3),sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_4607])).

cnf(c_25,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6440,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),X0_44),k7_setfam_1(u1_struct_0(sK3),sK4)) = iProver_top
    | r2_hidden(X0_44,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6073,c_25])).

cnf(c_6441,plain,
    ( r2_hidden(X0_44,sK4) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),X0_44),k7_setfam_1(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6440])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0,sK3)
    | ~ v1_tops_2(X1,sK3) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_528,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v3_pre_topc(X0,sK3)
    | ~ v1_tops_2(X1,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_514,c_19])).

cnf(c_2001,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v3_pre_topc(X0_44,sK3)
    | ~ v1_tops_2(X1_44,sK3) ),
    inference(subtyping,[status(esa)],[c_528])).

cnf(c_2660,plain,
    ( r2_hidden(X0_44,X1_44) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(X0_44,sK3) = iProver_top
    | v1_tops_2(X1_44,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_4314,plain,
    ( r2_hidden(X0_44,k7_setfam_1(u1_struct_0(sK3),X1_44)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(X0_44,sK3) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),X1_44),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2643,c_2660])).

cnf(c_7078,plain,
    ( r2_hidden(X0_44,k7_setfam_1(u1_struct_0(sK3),sK4)) != iProver_top
    | v3_pre_topc(X0_44,sK3) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_4314])).

cnf(c_21,negated_conjecture,
    ( v2_tops_2(sK4,sK3)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,plain,
    ( v2_tops_2(sK4,sK3) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v2_tops_2(X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_370,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v2_tops_2(X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_371,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ v2_tops_2(X1,sK3)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_385,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ v2_tops_2(X1,sK3)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_371,c_19])).

cnf(c_2010,plain,
    ( v4_pre_topc(X0_44,sK3)
    | ~ v2_tops_2(X1_44,sK3)
    | ~ r2_hidden(X0_44,X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_2651,plain,
    ( v4_pre_topc(X0_44,sK3) = iProver_top
    | v2_tops_2(X1_44,sK3) != iProver_top
    | r2_hidden(X0_44,X1_44) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_4174,plain,
    ( v4_pre_topc(X0_44,sK3) = iProver_top
    | v2_tops_2(sK4,sK3) != iProver_top
    | r2_hidden(X0_44,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_2651])).

cnf(c_20,negated_conjecture,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_188,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_498,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_499,plain,
    ( r2_hidden(sK0(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_587,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | r2_hidden(sK0(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | k7_setfam_1(u1_struct_0(sK3),sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_188,c_499])).

cnf(c_588,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_589,plain,
    ( v2_tops_2(sK4,sK3) != iProver_top
    | r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),sK4)) = iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,X0),sK3)
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_600,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,X0),sK3)
    | k7_setfam_1(u1_struct_0(sK3),sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_188,c_439])).

cnf(c_601,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_602,plain,
    ( v2_tops_2(sK4,sK3) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_613,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_setfam_1(u1_struct_0(sK3),sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_188,c_424])).

cnf(c_614,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_615,plain,
    ( v2_tops_2(sK4,sK3) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_2878,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_2879,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2878])).

cnf(c_17,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v3_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_468,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v3_pre_topc(X1,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_469,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_2004,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0_44,sK3) ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_3101,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3)
    | ~ m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_3102,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3101])).

cnf(c_3107,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44)
    | ~ r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),X0_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_3108,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44) = iProver_top
    | r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),X0_44)) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3107])).

cnf(c_3110,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK4) = iProver_top
    | r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),sK4)) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_3545,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3)
    | ~ v2_tops_2(X0_44,sK3)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_3551,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3) = iProver_top
    | v2_tops_2(X0_44,sK3) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3545])).

cnf(c_3553,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3) = iProver_top
    | v2_tops_2(sK4,sK3) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3551])).

cnf(c_4303,plain,
    ( v2_tops_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4174,c_25,c_589,c_602,c_615,c_2879,c_3102,c_3110,c_3553])).

cnf(c_7152,plain,
    ( v3_pre_topc(X0_44,sK3) = iProver_top
    | r2_hidden(X0_44,k7_setfam_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7078,c_25,c_26,c_589,c_602,c_615,c_2879,c_3102,c_3110,c_3553])).

cnf(c_7153,plain,
    ( r2_hidden(X0_44,k7_setfam_1(u1_struct_0(sK3),sK4)) != iProver_top
    | v3_pre_topc(X0_44,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7152])).

cnf(c_7165,plain,
    ( r2_hidden(X0_44,sK4) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6441,c_7153])).

cnf(c_15,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_355,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_356,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X0),sK3) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_2011,plain,
    ( v4_pre_topc(X0_44,sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_2650,plain,
    ( v4_pre_topc(X0_44,sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_7339,plain,
    ( v4_pre_topc(X0_44,sK3) = iProver_top
    | r2_hidden(X0_44,sK4) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7165,c_2650])).

cnf(c_2075,plain,
    ( v4_pre_topc(X0_44,sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_3141,plain,
    ( r2_hidden(X0_44,sK4) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_2645])).

cnf(c_7344,plain,
    ( r2_hidden(X0_44,sK4) != iProver_top
    | v4_pre_topc(X0_44,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7339,c_2075,c_3141,c_7165])).

cnf(c_7345,plain,
    ( v4_pre_topc(X0_44,sK3) = iProver_top
    | r2_hidden(X0_44,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7344])).

cnf(c_7352,plain,
    ( v4_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v2_tops_2(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3488,c_7345])).

cnf(c_4,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_483,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_484,plain,
    ( ~ v4_pre_topc(sK1(sK3,X0),sK3)
    | v2_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_2003,plain,
    ( ~ v4_pre_topc(sK1(sK3,X0_44),sK3)
    | v2_tops_2(X0_44,sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_2099,plain,
    ( v4_pre_topc(sK1(sK3,X0_44),sK3) != iProver_top
    | v2_tops_2(X0_44,sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_2101,plain,
    ( v4_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | v2_tops_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7352,c_4303,c_2101,c_25])).


%------------------------------------------------------------------------------
