%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1298+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 738 expanded)
%              Number of clauses        :  120 ( 244 expanded)
%              Number of leaves         :   15 ( 152 expanded)
%              Depth                    :   16
%              Number of atoms          :  734 (3746 expanded)
%              Number of equality atoms :  160 ( 274 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v2_tops_2(X1,X0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v2_tops_2(X1,X0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
      | ~ v2_tops_2(sK4,sK3) )
    & ( v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
      | v2_tops_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f39,f38])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
    | ~ v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
    | v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

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
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1854,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2473,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1854])).

cnf(c_6,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_535,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_536,plain,
    ( v2_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_1852,plain,
    ( v2_tops_2(X0_44,sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK1(sK3,X0_44),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_536])).

cnf(c_2475,plain,
    ( v2_tops_2(X0_44,sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(sK3,X0_44),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1852])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1858,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2469,plain,
    ( k3_subset_1(X0_45,k3_subset_1(X0_45,X0_44)) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1858])).

cnf(c_4231,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44))) = sK1(sK3,X0_44)
    | v2_tops_2(X0_44,sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2475,c_2469])).

cnf(c_6636,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4))) = sK1(sK3,sK4)
    | v2_tops_2(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2473,c_4231])).

cnf(c_24,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,plain,
    ( v2_tops_2(sK4,sK3) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4272,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4))) = sK1(sK3,sK4)
    | v2_tops_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4231])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1859,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X0_45)))
    | m1_subset_1(k7_setfam_1(X0_45,X0_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2468,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_45,X0_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1859])).

cnf(c_3008,plain,
    ( k3_subset_1(k1_zfmisc_1(X0_45),k3_subset_1(k1_zfmisc_1(X0_45),k7_setfam_1(X0_45,X0_44))) = k7_setfam_1(X0_45,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X0_45))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2468,c_2469])).

cnf(c_4441,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k7_setfam_1(u1_struct_0(sK3),sK4))) = k7_setfam_1(u1_struct_0(sK3),sK4) ),
    inference(superposition,[status(thm)],[c_2473,c_3008])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1860,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | m1_subset_1(k3_subset_1(X0_45,X0_44),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2467,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_45,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_4499,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_2467])).

cnf(c_2694,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_2695,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2694])).

cnf(c_4801,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4499,c_24,c_2695])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,X0),sK3)
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_1849,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,X0_44),sK3)
    | v1_tops_2(X0_44,sK3) ),
    inference(subtyping,[status(esa)],[c_581])).

cnf(c_2478,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(sK0(sK3,X0_44),sK3) != iProver_top
    | v1_tops_2(X0_44,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1849])).

cnf(c_4811,plain,
    ( v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4801,c_2478])).

cnf(c_20,negated_conjecture,
    ( v2_tops_2(sK4,sK3)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( v2_tops_2(sK4,sK3) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2680,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1849])).

cnf(c_2681,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2680])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_22])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_1850,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,X0_44),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_2(X0_44,sK3) ),
    inference(subtyping,[status(esa)],[c_566])).

cnf(c_2683,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_2684,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2683])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_640,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_641,plain,
    ( r2_hidden(sK0(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_1845,plain,
    ( r2_hidden(sK0(sK3,X0_44),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v1_tops_2(X0_44,sK3) ),
    inference(subtyping,[status(esa)],[c_641])).

cnf(c_2686,plain,
    ( r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_2687,plain,
    ( r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),sK4)) = iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2686])).

cnf(c_17,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v3_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_610,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v3_pre_topc(X1,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_611,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_1847,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0_44,sK3) ),
    inference(subtyping,[status(esa)],[c_611])).

cnf(c_3191,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3)
    | ~ m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_3192,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3191])).

cnf(c_3205,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1860])).

cnf(c_3206,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3205])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1861,plain,
    ( ~ r2_hidden(X0_44,k7_setfam_1(X0_45,X1_44))
    | r2_hidden(k3_subset_1(X0_45,X0_44),X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_45)))
    | ~ m1_subset_1(k7_setfam_1(X0_45,X1_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3203,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44)
    | ~ r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),X0_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1861])).

cnf(c_3210,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44) = iProver_top
    | r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),X0_44)) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3203])).

cnf(c_3212,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK4) = iProver_top
    | r2_hidden(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k7_setfam_1(u1_struct_0(sK3),sK4)) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3210])).

cnf(c_7,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v2_tops_2(X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_514,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v2_tops_2(X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_515,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ v2_tops_2(X1,sK3)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1853,plain,
    ( v4_pre_topc(X0_44,sK3)
    | ~ v2_tops_2(X1_44,sK3)
    | ~ r2_hidden(X0_44,X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_515])).

cnf(c_4618,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3)
    | ~ v2_tops_2(X0_44,sK3)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_4627,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3) = iProver_top
    | v2_tops_2(X0_44,sK3) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),X0_44) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4618])).

cnf(c_4629,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK3) = iProver_top
    | v2_tops_2(sK4,sK3) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),sK4) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK0(sK3,k7_setfam_1(u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4627])).

cnf(c_4909,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4811,c_24,c_25,c_2681,c_2684,c_2687,c_2695,c_3192,c_3206,c_3212,c_4629])).

cnf(c_6820,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4))) = sK1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6636,c_24,c_25,c_26,c_2681,c_2684,c_2687,c_2695,c_3192,c_3206,c_3212,c_4272,c_4629])).

cnf(c_18,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_595,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_pre_topc(X1,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_596,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_1848,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X0_44,sK3) ),
    inference(subtyping,[status(esa)],[c_596])).

cnf(c_2479,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),X0_44),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(X0_44,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1848])).

cnf(c_6829,plain,
    ( v4_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6820,c_2479])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_655,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_656,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0,sK3)
    | ~ v1_tops_2(X1,sK3) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_1844,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(X0_44,sK3)
    | ~ v1_tops_2(X1_44,sK3) ),
    inference(subtyping,[status(esa)],[c_656])).

cnf(c_3097,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),sK3)
    | ~ v1_tops_2(X1_44,sK3) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_4366,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k7_setfam_1(u1_struct_0(sK3),X1_44))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X1_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),sK3)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),X1_44),sK3) ),
    inference(instantiation,[status(thm)],[c_3097])).

cnf(c_4367,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k7_setfam_1(u1_struct_0(sK3),X1_44)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X1_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),sK3) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),X1_44),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4366])).

cnf(c_4369,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),k7_setfam_1(u1_struct_0(sK3),sK4)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),sK3) = iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4367])).

cnf(c_1872,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | r2_hidden(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_2939,plain,
    ( r2_hidden(X0_44,X1_44)
    | ~ r2_hidden(sK1(sK3,X2_44),X2_44)
    | X1_44 != X2_44
    | X0_44 != sK1(sK3,X2_44) ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_3667,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44))),X1_44)
    | ~ r2_hidden(sK1(sK3,X0_44),X0_44)
    | X1_44 != X0_44
    | k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44))) != sK1(sK3,X0_44) ),
    inference(instantiation,[status(thm)],[c_2939])).

cnf(c_3668,plain,
    ( X0_44 != X1_44
    | k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,X1_44))) != sK1(sK3,X1_44)
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,X1_44))),X0_44) = iProver_top
    | r2_hidden(sK1(sK3,X1_44),X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3667])).

cnf(c_3670,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4))) != sK1(sK3,sK4)
    | sK4 != sK4
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4))),sK4) = iProver_top
    | r2_hidden(sK1(sK3,sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3668])).

cnf(c_11,plain,
    ( r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1862,plain,
    ( r2_hidden(X0_44,k7_setfam_1(X0_45,X1_44))
    | ~ r2_hidden(k3_subset_1(X0_45,X0_44),X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_45)))
    | ~ m1_subset_1(k7_setfam_1(X0_45,X1_44),k1_zfmisc_1(k1_zfmisc_1(X0_45))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3111,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44))),X1_44)
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k7_setfam_1(u1_struct_0(sK3),X1_44))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X1_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_3127,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44))),X1_44) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k7_setfam_1(u1_struct_0(sK3),X1_44)) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),X1_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3111])).

cnf(c_3129,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4))),sK4) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),k7_setfam_1(u1_struct_0(sK3),sK4)) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_setfam_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3127])).

cnf(c_2917,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X0_44),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1860])).

cnf(c_2918,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,X0_44)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK1(sK3,X0_44),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2917])).

cnf(c_2920,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2918])).

cnf(c_1867,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1886,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_182,plain,
    ( ~ v2_tops_2(sK4,sK3)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_1092,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
    | sK4 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_536])).

cnf(c_1093,plain,
    ( m1_subset_1(sK1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(unflattening,[status(thm)],[c_1092])).

cnf(c_1094,plain,
    ( m1_subset_1(sK1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_5,plain,
    ( v2_tops_2(X0,X1)
    | r2_hidden(sK1(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_550,plain,
    ( v2_tops_2(X0,X1)
    | r2_hidden(sK1(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_551,plain,
    ( v2_tops_2(X0,sK3)
    | r2_hidden(sK1(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_1078,plain,
    ( r2_hidden(sK1(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
    | sK4 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_551])).

cnf(c_1079,plain,
    ( r2_hidden(sK1(sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(unflattening,[status(thm)],[c_1078])).

cnf(c_1080,plain,
    ( r2_hidden(sK1(sK3,sK4),sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_4,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_625,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_626,plain,
    ( ~ v4_pre_topc(sK1(sK3,X0),sK3)
    | v2_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_1064,plain,
    ( ~ v4_pre_topc(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3)
    | sK4 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_626])).

cnf(c_1065,plain,
    ( ~ v4_pre_topc(sK1(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(unflattening,[status(thm)],[c_1064])).

cnf(c_1066,plain,
    ( v4_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6829,c_4909,c_4369,c_4272,c_3670,c_3129,c_2920,c_2695,c_1886,c_1094,c_1080,c_1066,c_26,c_24])).


%------------------------------------------------------------------------------
