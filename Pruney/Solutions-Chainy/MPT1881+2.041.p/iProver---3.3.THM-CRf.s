%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:18 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  213 (2018 expanded)
%              Number of clauses        :  136 ( 614 expanded)
%              Number of leaves         :   22 ( 432 expanded)
%              Depth                    :   22
%              Number of atoms          :  769 (11372 expanded)
%              Number of equality atoms :  195 ( 730 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK3,u1_struct_0(X0))
          | ~ v3_tex_2(sK3,X0) )
        & ( ~ v1_subset_1(sK3,u1_struct_0(X0))
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK2))
            | ~ v3_tex_2(X1,sK2) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK2))
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ( v1_subset_1(sK3,u1_struct_0(sK2))
      | ~ v3_tex_2(sK3,sK2) )
    & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f69,f71,f70])).

fof(f113,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f112,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f72])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f114,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f111,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_tex_2(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK0(X0,X1) != X1
                & r1_tarski(X1,sK0(X0,X1))
                & v2_tex_2(sK0(X0,X1),X0)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f61,f62])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f108,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f109,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f110,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_1(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_324,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_412,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_22,c_324])).

cnf(c_36,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_326,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_36])).

cnf(c_741,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_412,c_326])).

cnf(c_742,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ r1_tarski(sK3,u1_struct_0(sK2))
    | u1_struct_0(sK2) = sK3 ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_2784,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_743,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3083,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3084,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3083])).

cnf(c_23,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_35,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_328,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_35])).

cnf(c_754,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK2) != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_328])).

cnf(c_755,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_2783,plain,
    ( sK3 != u1_struct_0(sK2)
    | v3_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_45,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_118,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_120,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_8,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_121,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_123,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_10,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_722,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | k2_struct_0(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_328])).

cnf(c_723,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | k2_struct_0(X0) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_725,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k2_struct_0(sK2) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_2148,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_2160,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_2140,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2167,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_407,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_324])).

cnf(c_3175,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK2))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_3177,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3175])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3109,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK2),X0),k3_subset_1(u1_struct_0(sK2),sK3))
    | r1_tarski(sK3,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3196,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK2),k2_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK3))
    | r1_tarski(sK3,k2_struct_0(sK2))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3109])).

cnf(c_3197,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK2),k2_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK3)) != iProver_top
    | r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3196])).

cnf(c_2788,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | X1 != X2
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_842,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_983,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_842,c_38])).

cnf(c_984,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k4_subset_1(u1_struct_0(sK2),X0,k3_subset_1(u1_struct_0(sK2),X0)) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_983])).

cnf(c_2779,plain,
    ( k4_subset_1(u1_struct_0(sK2),X0,k3_subset_1(u1_struct_0(sK2),X0)) = k2_struct_0(sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_3102,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK3,k3_subset_1(u1_struct_0(sK2),sK3)) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2788,c_2779])).

cnf(c_3,plain,
    ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2791,plain,
    ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3270,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK2),k2_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK3)) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_2791])).

cnf(c_815,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_8])).

cnf(c_946,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_815,c_38])).

cnf(c_947,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_2782,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_28,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1016,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_38])).

cnf(c_1017,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_33,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_590,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_591,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_39,negated_conjecture,
    ( v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_595,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_40,c_39,c_38])).

cnf(c_596,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_1021,plain,
    ( ~ v3_tex_2(X1,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_40,c_39,c_38,c_591])).

cnf(c_1022,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_2777,plain,
    ( X0 = X1
    | v3_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_4182,plain,
    ( sK3 = X0
    | v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_2777])).

cnf(c_4238,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2782,c_4182])).

cnf(c_5235,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2783,c_45,c_46,c_120,c_123,c_725,c_2160,c_2167,c_3084,c_3177,c_3197,c_3270,c_4238])).

cnf(c_5677,plain,
    ( u1_struct_0(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2784,c_45,c_46,c_120,c_123,c_725,c_743,c_2160,c_2167,c_3084,c_3177,c_3197,c_3270,c_4238])).

cnf(c_2789,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3166,plain,
    ( r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2782,c_2789])).

cnf(c_707,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ l1_struct_0(X2)
    | X1 = X0
    | u1_struct_0(X2) != X1
    | k2_struct_0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_412])).

cnf(c_708,plain,
    ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_801,plain,
    ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_708])).

cnf(c_953,plain,
    ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
    | u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_801,c_38])).

cnf(c_954,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
    | u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_953])).

cnf(c_2781,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_3887,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3166,c_2781])).

cnf(c_5680,plain,
    ( k2_struct_0(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_5677,c_3887])).

cnf(c_18,plain,
    ( v1_tops_1(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_976,plain,
    ( v1_tops_1(k2_struct_0(X0),X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_977,plain,
    ( v1_tops_1(k2_struct_0(sK2),sK2) ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_2780,plain,
    ( v1_tops_1(k2_struct_0(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_2790,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_34,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_566,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_41])).

cnf(c_567,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_571,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_40,c_38])).

cnf(c_606,plain,
    ( v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_596,c_571])).

cnf(c_2786,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | v1_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_6085,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | v1_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2786,c_5677])).

cnf(c_6092,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | v1_tops_1(X0,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2790,c_6085])).

cnf(c_6601,plain,
    ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
    | r1_tarski(k2_struct_0(sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_6092])).

cnf(c_91,plain,
    ( v1_tops_1(k2_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_93,plain,
    ( v1_tops_1(k2_struct_0(sK2),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_119,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_122,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_710,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1557,plain,
    ( ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) != sK3
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_755,c_606])).

cnf(c_1558,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) != sK3 ),
    inference(unflattening,[status(thm)],[c_1557])).

cnf(c_20,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1142,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_38])).

cnf(c_1143,plain,
    ( v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1142])).

cnf(c_3027,plain,
    ( v1_tops_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_3086,plain,
    ( r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3415,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_21,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1127,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_1128,plain,
    ( ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1127])).

cnf(c_2773,plain,
    ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | v1_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_3586,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
    | v1_tops_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_2773])).

cnf(c_19,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ r1_tarski(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1157,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ r1_tarski(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_1158,plain,
    ( ~ v1_tops_1(X0,sK2)
    | v1_tops_1(X1,sK2)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_1157])).

cnf(c_3054,plain,
    ( v1_tops_1(X0,sK2)
    | ~ v1_tops_1(k2_struct_0(sK2),sK2)
    | ~ r1_tarski(k2_struct_0(sK2),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_3647,plain,
    ( ~ v1_tops_1(k2_struct_0(sK2),sK2)
    | v1_tops_1(sK3,sK2)
    | ~ r1_tarski(k2_struct_0(sK2),sK3)
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3054])).

cnf(c_3648,plain,
    ( v1_tops_1(k2_struct_0(sK2),sK2) != iProver_top
    | v1_tops_1(sK3,sK2) = iProver_top
    | r1_tarski(k2_struct_0(sK2),sK3) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3647])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3094,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != k2_struct_0(sK2)
    | X1 != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_3484,plain,
    ( m1_subset_1(u1_struct_0(sK2),X0)
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3094])).

cnf(c_4535,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) != k2_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_7205,plain,
    ( r1_tarski(k2_struct_0(sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6601,c_38,c_45,c_37,c_46,c_93,c_119,c_120,c_122,c_123,c_710,c_725,c_743,c_1558,c_2160,c_2167,c_3027,c_3084,c_3086,c_3177,c_3197,c_3270,c_3415,c_3586,c_3648,c_4238,c_4535])).

cnf(c_10538,plain,
    ( r1_tarski(sK3,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5680,c_7205])).

cnf(c_3165,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_2789])).

cnf(c_4824,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3887,c_3165])).

cnf(c_10555,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5680,c_4824])).

cnf(c_10626,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10538,c_10555])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.32/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.02  
% 3.32/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/1.02  
% 3.32/1.02  ------  iProver source info
% 3.32/1.02  
% 3.32/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.32/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/1.02  git: non_committed_changes: false
% 3.32/1.02  git: last_make_outside_of_git: false
% 3.32/1.02  
% 3.32/1.02  ------ 
% 3.32/1.02  
% 3.32/1.02  ------ Input Options
% 3.32/1.02  
% 3.32/1.02  --out_options                           all
% 3.32/1.02  --tptp_safe_out                         true
% 3.32/1.02  --problem_path                          ""
% 3.32/1.02  --include_path                          ""
% 3.32/1.02  --clausifier                            res/vclausify_rel
% 3.32/1.02  --clausifier_options                    --mode clausify
% 3.32/1.02  --stdin                                 false
% 3.32/1.02  --stats_out                             all
% 3.32/1.02  
% 3.32/1.02  ------ General Options
% 3.32/1.02  
% 3.32/1.02  --fof                                   false
% 3.32/1.02  --time_out_real                         305.
% 3.32/1.02  --time_out_virtual                      -1.
% 3.32/1.02  --symbol_type_check                     false
% 3.32/1.02  --clausify_out                          false
% 3.32/1.02  --sig_cnt_out                           false
% 3.32/1.02  --trig_cnt_out                          false
% 3.32/1.02  --trig_cnt_out_tolerance                1.
% 3.32/1.02  --trig_cnt_out_sk_spl                   false
% 3.32/1.02  --abstr_cl_out                          false
% 3.32/1.02  
% 3.32/1.02  ------ Global Options
% 3.32/1.02  
% 3.32/1.02  --schedule                              default
% 3.32/1.02  --add_important_lit                     false
% 3.32/1.02  --prop_solver_per_cl                    1000
% 3.32/1.02  --min_unsat_core                        false
% 3.32/1.02  --soft_assumptions                      false
% 3.32/1.02  --soft_lemma_size                       3
% 3.32/1.02  --prop_impl_unit_size                   0
% 3.32/1.02  --prop_impl_unit                        []
% 3.32/1.02  --share_sel_clauses                     true
% 3.32/1.02  --reset_solvers                         false
% 3.32/1.02  --bc_imp_inh                            [conj_cone]
% 3.32/1.02  --conj_cone_tolerance                   3.
% 3.32/1.02  --extra_neg_conj                        none
% 3.32/1.02  --large_theory_mode                     true
% 3.32/1.02  --prolific_symb_bound                   200
% 3.32/1.02  --lt_threshold                          2000
% 3.32/1.02  --clause_weak_htbl                      true
% 3.32/1.02  --gc_record_bc_elim                     false
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing Options
% 3.32/1.02  
% 3.32/1.02  --preprocessing_flag                    true
% 3.32/1.02  --time_out_prep_mult                    0.1
% 3.32/1.02  --splitting_mode                        input
% 3.32/1.02  --splitting_grd                         true
% 3.32/1.02  --splitting_cvd                         false
% 3.32/1.02  --splitting_cvd_svl                     false
% 3.32/1.02  --splitting_nvd                         32
% 3.32/1.02  --sub_typing                            true
% 3.32/1.02  --prep_gs_sim                           true
% 3.32/1.02  --prep_unflatten                        true
% 3.32/1.02  --prep_res_sim                          true
% 3.32/1.02  --prep_upred                            true
% 3.32/1.02  --prep_sem_filter                       exhaustive
% 3.32/1.02  --prep_sem_filter_out                   false
% 3.32/1.02  --pred_elim                             true
% 3.32/1.02  --res_sim_input                         true
% 3.32/1.02  --eq_ax_congr_red                       true
% 3.32/1.02  --pure_diseq_elim                       true
% 3.32/1.02  --brand_transform                       false
% 3.32/1.02  --non_eq_to_eq                          false
% 3.32/1.02  --prep_def_merge                        true
% 3.32/1.02  --prep_def_merge_prop_impl              false
% 3.32/1.02  --prep_def_merge_mbd                    true
% 3.32/1.02  --prep_def_merge_tr_red                 false
% 3.32/1.02  --prep_def_merge_tr_cl                  false
% 3.32/1.02  --smt_preprocessing                     true
% 3.32/1.02  --smt_ac_axioms                         fast
% 3.32/1.02  --preprocessed_out                      false
% 3.32/1.02  --preprocessed_stats                    false
% 3.32/1.02  
% 3.32/1.02  ------ Abstraction refinement Options
% 3.32/1.02  
% 3.32/1.02  --abstr_ref                             []
% 3.32/1.02  --abstr_ref_prep                        false
% 3.32/1.02  --abstr_ref_until_sat                   false
% 3.32/1.02  --abstr_ref_sig_restrict                funpre
% 3.32/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.02  --abstr_ref_under                       []
% 3.32/1.02  
% 3.32/1.02  ------ SAT Options
% 3.32/1.02  
% 3.32/1.02  --sat_mode                              false
% 3.32/1.02  --sat_fm_restart_options                ""
% 3.32/1.02  --sat_gr_def                            false
% 3.32/1.02  --sat_epr_types                         true
% 3.32/1.02  --sat_non_cyclic_types                  false
% 3.32/1.02  --sat_finite_models                     false
% 3.32/1.02  --sat_fm_lemmas                         false
% 3.32/1.02  --sat_fm_prep                           false
% 3.32/1.02  --sat_fm_uc_incr                        true
% 3.32/1.02  --sat_out_model                         small
% 3.32/1.02  --sat_out_clauses                       false
% 3.32/1.02  
% 3.32/1.02  ------ QBF Options
% 3.32/1.02  
% 3.32/1.02  --qbf_mode                              false
% 3.32/1.02  --qbf_elim_univ                         false
% 3.32/1.02  --qbf_dom_inst                          none
% 3.32/1.02  --qbf_dom_pre_inst                      false
% 3.32/1.02  --qbf_sk_in                             false
% 3.32/1.02  --qbf_pred_elim                         true
% 3.32/1.02  --qbf_split                             512
% 3.32/1.02  
% 3.32/1.02  ------ BMC1 Options
% 3.32/1.02  
% 3.32/1.02  --bmc1_incremental                      false
% 3.32/1.02  --bmc1_axioms                           reachable_all
% 3.32/1.02  --bmc1_min_bound                        0
% 3.32/1.02  --bmc1_max_bound                        -1
% 3.32/1.02  --bmc1_max_bound_default                -1
% 3.32/1.02  --bmc1_symbol_reachability              true
% 3.32/1.02  --bmc1_property_lemmas                  false
% 3.32/1.02  --bmc1_k_induction                      false
% 3.32/1.02  --bmc1_non_equiv_states                 false
% 3.32/1.02  --bmc1_deadlock                         false
% 3.32/1.02  --bmc1_ucm                              false
% 3.32/1.02  --bmc1_add_unsat_core                   none
% 3.32/1.02  --bmc1_unsat_core_children              false
% 3.32/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.02  --bmc1_out_stat                         full
% 3.32/1.02  --bmc1_ground_init                      false
% 3.32/1.02  --bmc1_pre_inst_next_state              false
% 3.32/1.02  --bmc1_pre_inst_state                   false
% 3.32/1.02  --bmc1_pre_inst_reach_state             false
% 3.32/1.02  --bmc1_out_unsat_core                   false
% 3.32/1.02  --bmc1_aig_witness_out                  false
% 3.32/1.02  --bmc1_verbose                          false
% 3.32/1.02  --bmc1_dump_clauses_tptp                false
% 3.32/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.02  --bmc1_dump_file                        -
% 3.32/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.02  --bmc1_ucm_extend_mode                  1
% 3.32/1.02  --bmc1_ucm_init_mode                    2
% 3.32/1.02  --bmc1_ucm_cone_mode                    none
% 3.32/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.02  --bmc1_ucm_relax_model                  4
% 3.32/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.02  --bmc1_ucm_layered_model                none
% 3.32/1.02  --bmc1_ucm_max_lemma_size               10
% 3.32/1.02  
% 3.32/1.02  ------ AIG Options
% 3.32/1.02  
% 3.32/1.02  --aig_mode                              false
% 3.32/1.02  
% 3.32/1.02  ------ Instantiation Options
% 3.32/1.02  
% 3.32/1.02  --instantiation_flag                    true
% 3.32/1.02  --inst_sos_flag                         false
% 3.32/1.02  --inst_sos_phase                        true
% 3.32/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel_side                     num_symb
% 3.32/1.02  --inst_solver_per_active                1400
% 3.32/1.02  --inst_solver_calls_frac                1.
% 3.32/1.02  --inst_passive_queue_type               priority_queues
% 3.32/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.02  --inst_passive_queues_freq              [25;2]
% 3.32/1.02  --inst_dismatching                      true
% 3.32/1.02  --inst_eager_unprocessed_to_passive     true
% 3.32/1.02  --inst_prop_sim_given                   true
% 3.32/1.02  --inst_prop_sim_new                     false
% 3.32/1.02  --inst_subs_new                         false
% 3.32/1.02  --inst_eq_res_simp                      false
% 3.32/1.02  --inst_subs_given                       false
% 3.32/1.02  --inst_orphan_elimination               true
% 3.32/1.02  --inst_learning_loop_flag               true
% 3.32/1.02  --inst_learning_start                   3000
% 3.32/1.02  --inst_learning_factor                  2
% 3.32/1.02  --inst_start_prop_sim_after_learn       3
% 3.32/1.02  --inst_sel_renew                        solver
% 3.32/1.02  --inst_lit_activity_flag                true
% 3.32/1.02  --inst_restr_to_given                   false
% 3.32/1.02  --inst_activity_threshold               500
% 3.32/1.02  --inst_out_proof                        true
% 3.32/1.02  
% 3.32/1.02  ------ Resolution Options
% 3.32/1.02  
% 3.32/1.02  --resolution_flag                       true
% 3.32/1.02  --res_lit_sel                           adaptive
% 3.32/1.02  --res_lit_sel_side                      none
% 3.32/1.02  --res_ordering                          kbo
% 3.32/1.02  --res_to_prop_solver                    active
% 3.32/1.02  --res_prop_simpl_new                    false
% 3.32/1.02  --res_prop_simpl_given                  true
% 3.32/1.02  --res_passive_queue_type                priority_queues
% 3.32/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.02  --res_passive_queues_freq               [15;5]
% 3.32/1.02  --res_forward_subs                      full
% 3.32/1.02  --res_backward_subs                     full
% 3.32/1.02  --res_forward_subs_resolution           true
% 3.32/1.02  --res_backward_subs_resolution          true
% 3.32/1.02  --res_orphan_elimination                true
% 3.32/1.02  --res_time_limit                        2.
% 3.32/1.02  --res_out_proof                         true
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Options
% 3.32/1.02  
% 3.32/1.02  --superposition_flag                    true
% 3.32/1.02  --sup_passive_queue_type                priority_queues
% 3.32/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.32/1.02  --demod_completeness_check              fast
% 3.32/1.02  --demod_use_ground                      true
% 3.32/1.02  --sup_to_prop_solver                    passive
% 3.32/1.02  --sup_prop_simpl_new                    true
% 3.32/1.02  --sup_prop_simpl_given                  true
% 3.32/1.02  --sup_fun_splitting                     false
% 3.32/1.02  --sup_smt_interval                      50000
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Simplification Setup
% 3.32/1.02  
% 3.32/1.02  --sup_indices_passive                   []
% 3.32/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.02  --sup_full_bw                           [BwDemod]
% 3.32/1.02  --sup_immed_triv                        [TrivRules]
% 3.32/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.02  --sup_immed_bw_main                     []
% 3.32/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.02  
% 3.32/1.02  ------ Combination Options
% 3.32/1.02  
% 3.32/1.02  --comb_res_mult                         3
% 3.32/1.02  --comb_sup_mult                         2
% 3.32/1.02  --comb_inst_mult                        10
% 3.32/1.02  
% 3.32/1.02  ------ Debug Options
% 3.32/1.02  
% 3.32/1.02  --dbg_backtrace                         false
% 3.32/1.02  --dbg_dump_prop_clauses                 false
% 3.32/1.02  --dbg_dump_prop_clauses_file            -
% 3.32/1.02  --dbg_out_stat                          false
% 3.32/1.02  ------ Parsing...
% 3.32/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/1.02  ------ Proving...
% 3.32/1.02  ------ Problem Properties 
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  clauses                                 27
% 3.32/1.02  conjectures                             1
% 3.32/1.02  EPR                                     0
% 3.32/1.02  Horn                                    24
% 3.32/1.02  unary                                   3
% 3.32/1.02  binary                                  8
% 3.32/1.02  lits                                    77
% 3.32/1.02  lits eq                                 15
% 3.32/1.02  fd_pure                                 0
% 3.32/1.02  fd_pseudo                               0
% 3.32/1.02  fd_cond                                 0
% 3.32/1.02  fd_pseudo_cond                          1
% 3.32/1.02  AC symbols                              0
% 3.32/1.02  
% 3.32/1.02  ------ Schedule dynamic 5 is on 
% 3.32/1.02  
% 3.32/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  ------ 
% 3.32/1.02  Current options:
% 3.32/1.02  ------ 
% 3.32/1.02  
% 3.32/1.02  ------ Input Options
% 3.32/1.02  
% 3.32/1.02  --out_options                           all
% 3.32/1.02  --tptp_safe_out                         true
% 3.32/1.02  --problem_path                          ""
% 3.32/1.02  --include_path                          ""
% 3.32/1.02  --clausifier                            res/vclausify_rel
% 3.32/1.02  --clausifier_options                    --mode clausify
% 3.32/1.02  --stdin                                 false
% 3.32/1.02  --stats_out                             all
% 3.32/1.02  
% 3.32/1.02  ------ General Options
% 3.32/1.02  
% 3.32/1.02  --fof                                   false
% 3.32/1.02  --time_out_real                         305.
% 3.32/1.02  --time_out_virtual                      -1.
% 3.32/1.02  --symbol_type_check                     false
% 3.32/1.02  --clausify_out                          false
% 3.32/1.02  --sig_cnt_out                           false
% 3.32/1.02  --trig_cnt_out                          false
% 3.32/1.02  --trig_cnt_out_tolerance                1.
% 3.32/1.02  --trig_cnt_out_sk_spl                   false
% 3.32/1.02  --abstr_cl_out                          false
% 3.32/1.02  
% 3.32/1.02  ------ Global Options
% 3.32/1.02  
% 3.32/1.02  --schedule                              default
% 3.32/1.02  --add_important_lit                     false
% 3.32/1.02  --prop_solver_per_cl                    1000
% 3.32/1.02  --min_unsat_core                        false
% 3.32/1.02  --soft_assumptions                      false
% 3.32/1.02  --soft_lemma_size                       3
% 3.32/1.02  --prop_impl_unit_size                   0
% 3.32/1.02  --prop_impl_unit                        []
% 3.32/1.02  --share_sel_clauses                     true
% 3.32/1.02  --reset_solvers                         false
% 3.32/1.02  --bc_imp_inh                            [conj_cone]
% 3.32/1.02  --conj_cone_tolerance                   3.
% 3.32/1.02  --extra_neg_conj                        none
% 3.32/1.02  --large_theory_mode                     true
% 3.32/1.02  --prolific_symb_bound                   200
% 3.32/1.02  --lt_threshold                          2000
% 3.32/1.02  --clause_weak_htbl                      true
% 3.32/1.02  --gc_record_bc_elim                     false
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing Options
% 3.32/1.02  
% 3.32/1.02  --preprocessing_flag                    true
% 3.32/1.02  --time_out_prep_mult                    0.1
% 3.32/1.02  --splitting_mode                        input
% 3.32/1.02  --splitting_grd                         true
% 3.32/1.02  --splitting_cvd                         false
% 3.32/1.02  --splitting_cvd_svl                     false
% 3.32/1.02  --splitting_nvd                         32
% 3.32/1.02  --sub_typing                            true
% 3.32/1.02  --prep_gs_sim                           true
% 3.32/1.02  --prep_unflatten                        true
% 3.32/1.02  --prep_res_sim                          true
% 3.32/1.02  --prep_upred                            true
% 3.32/1.02  --prep_sem_filter                       exhaustive
% 3.32/1.02  --prep_sem_filter_out                   false
% 3.32/1.02  --pred_elim                             true
% 3.32/1.02  --res_sim_input                         true
% 3.32/1.02  --eq_ax_congr_red                       true
% 3.32/1.02  --pure_diseq_elim                       true
% 3.32/1.02  --brand_transform                       false
% 3.32/1.02  --non_eq_to_eq                          false
% 3.32/1.02  --prep_def_merge                        true
% 3.32/1.02  --prep_def_merge_prop_impl              false
% 3.32/1.02  --prep_def_merge_mbd                    true
% 3.32/1.02  --prep_def_merge_tr_red                 false
% 3.32/1.02  --prep_def_merge_tr_cl                  false
% 3.32/1.02  --smt_preprocessing                     true
% 3.32/1.02  --smt_ac_axioms                         fast
% 3.32/1.02  --preprocessed_out                      false
% 3.32/1.02  --preprocessed_stats                    false
% 3.32/1.02  
% 3.32/1.02  ------ Abstraction refinement Options
% 3.32/1.02  
% 3.32/1.02  --abstr_ref                             []
% 3.32/1.02  --abstr_ref_prep                        false
% 3.32/1.02  --abstr_ref_until_sat                   false
% 3.32/1.02  --abstr_ref_sig_restrict                funpre
% 3.32/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.02  --abstr_ref_under                       []
% 3.32/1.02  
% 3.32/1.02  ------ SAT Options
% 3.32/1.02  
% 3.32/1.02  --sat_mode                              false
% 3.32/1.02  --sat_fm_restart_options                ""
% 3.32/1.02  --sat_gr_def                            false
% 3.32/1.02  --sat_epr_types                         true
% 3.32/1.02  --sat_non_cyclic_types                  false
% 3.32/1.02  --sat_finite_models                     false
% 3.32/1.02  --sat_fm_lemmas                         false
% 3.32/1.02  --sat_fm_prep                           false
% 3.32/1.02  --sat_fm_uc_incr                        true
% 3.32/1.02  --sat_out_model                         small
% 3.32/1.02  --sat_out_clauses                       false
% 3.32/1.02  
% 3.32/1.02  ------ QBF Options
% 3.32/1.02  
% 3.32/1.02  --qbf_mode                              false
% 3.32/1.02  --qbf_elim_univ                         false
% 3.32/1.02  --qbf_dom_inst                          none
% 3.32/1.02  --qbf_dom_pre_inst                      false
% 3.32/1.02  --qbf_sk_in                             false
% 3.32/1.02  --qbf_pred_elim                         true
% 3.32/1.02  --qbf_split                             512
% 3.32/1.02  
% 3.32/1.02  ------ BMC1 Options
% 3.32/1.02  
% 3.32/1.02  --bmc1_incremental                      false
% 3.32/1.02  --bmc1_axioms                           reachable_all
% 3.32/1.02  --bmc1_min_bound                        0
% 3.32/1.02  --bmc1_max_bound                        -1
% 3.32/1.02  --bmc1_max_bound_default                -1
% 3.32/1.02  --bmc1_symbol_reachability              true
% 3.32/1.02  --bmc1_property_lemmas                  false
% 3.32/1.02  --bmc1_k_induction                      false
% 3.32/1.02  --bmc1_non_equiv_states                 false
% 3.32/1.02  --bmc1_deadlock                         false
% 3.32/1.02  --bmc1_ucm                              false
% 3.32/1.02  --bmc1_add_unsat_core                   none
% 3.32/1.02  --bmc1_unsat_core_children              false
% 3.32/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.02  --bmc1_out_stat                         full
% 3.32/1.02  --bmc1_ground_init                      false
% 3.32/1.02  --bmc1_pre_inst_next_state              false
% 3.32/1.02  --bmc1_pre_inst_state                   false
% 3.32/1.02  --bmc1_pre_inst_reach_state             false
% 3.32/1.02  --bmc1_out_unsat_core                   false
% 3.32/1.02  --bmc1_aig_witness_out                  false
% 3.32/1.02  --bmc1_verbose                          false
% 3.32/1.02  --bmc1_dump_clauses_tptp                false
% 3.32/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.02  --bmc1_dump_file                        -
% 3.32/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.02  --bmc1_ucm_extend_mode                  1
% 3.32/1.02  --bmc1_ucm_init_mode                    2
% 3.32/1.02  --bmc1_ucm_cone_mode                    none
% 3.32/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.02  --bmc1_ucm_relax_model                  4
% 3.32/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.02  --bmc1_ucm_layered_model                none
% 3.32/1.02  --bmc1_ucm_max_lemma_size               10
% 3.32/1.02  
% 3.32/1.02  ------ AIG Options
% 3.32/1.02  
% 3.32/1.02  --aig_mode                              false
% 3.32/1.02  
% 3.32/1.02  ------ Instantiation Options
% 3.32/1.02  
% 3.32/1.02  --instantiation_flag                    true
% 3.32/1.02  --inst_sos_flag                         false
% 3.32/1.02  --inst_sos_phase                        true
% 3.32/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel_side                     none
% 3.32/1.02  --inst_solver_per_active                1400
% 3.32/1.02  --inst_solver_calls_frac                1.
% 3.32/1.02  --inst_passive_queue_type               priority_queues
% 3.32/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.02  --inst_passive_queues_freq              [25;2]
% 3.32/1.02  --inst_dismatching                      true
% 3.32/1.02  --inst_eager_unprocessed_to_passive     true
% 3.32/1.02  --inst_prop_sim_given                   true
% 3.32/1.02  --inst_prop_sim_new                     false
% 3.32/1.02  --inst_subs_new                         false
% 3.32/1.02  --inst_eq_res_simp                      false
% 3.32/1.02  --inst_subs_given                       false
% 3.32/1.02  --inst_orphan_elimination               true
% 3.32/1.02  --inst_learning_loop_flag               true
% 3.32/1.02  --inst_learning_start                   3000
% 3.32/1.02  --inst_learning_factor                  2
% 3.32/1.02  --inst_start_prop_sim_after_learn       3
% 3.32/1.02  --inst_sel_renew                        solver
% 3.32/1.02  --inst_lit_activity_flag                true
% 3.32/1.02  --inst_restr_to_given                   false
% 3.32/1.02  --inst_activity_threshold               500
% 3.32/1.02  --inst_out_proof                        true
% 3.32/1.02  
% 3.32/1.02  ------ Resolution Options
% 3.32/1.02  
% 3.32/1.02  --resolution_flag                       false
% 3.32/1.02  --res_lit_sel                           adaptive
% 3.32/1.02  --res_lit_sel_side                      none
% 3.32/1.02  --res_ordering                          kbo
% 3.32/1.02  --res_to_prop_solver                    active
% 3.32/1.02  --res_prop_simpl_new                    false
% 3.32/1.02  --res_prop_simpl_given                  true
% 3.32/1.02  --res_passive_queue_type                priority_queues
% 3.32/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.02  --res_passive_queues_freq               [15;5]
% 3.32/1.02  --res_forward_subs                      full
% 3.32/1.02  --res_backward_subs                     full
% 3.32/1.02  --res_forward_subs_resolution           true
% 3.32/1.02  --res_backward_subs_resolution          true
% 3.32/1.02  --res_orphan_elimination                true
% 3.32/1.02  --res_time_limit                        2.
% 3.32/1.02  --res_out_proof                         true
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Options
% 3.32/1.02  
% 3.32/1.02  --superposition_flag                    true
% 3.32/1.02  --sup_passive_queue_type                priority_queues
% 3.32/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.32/1.02  --demod_completeness_check              fast
% 3.32/1.02  --demod_use_ground                      true
% 3.32/1.02  --sup_to_prop_solver                    passive
% 3.32/1.02  --sup_prop_simpl_new                    true
% 3.32/1.02  --sup_prop_simpl_given                  true
% 3.32/1.02  --sup_fun_splitting                     false
% 3.32/1.02  --sup_smt_interval                      50000
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Simplification Setup
% 3.32/1.02  
% 3.32/1.02  --sup_indices_passive                   []
% 3.32/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.02  --sup_full_bw                           [BwDemod]
% 3.32/1.02  --sup_immed_triv                        [TrivRules]
% 3.32/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.03  --sup_immed_bw_main                     []
% 3.32/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.03  
% 3.32/1.03  ------ Combination Options
% 3.32/1.03  
% 3.32/1.03  --comb_res_mult                         3
% 3.32/1.03  --comb_sup_mult                         2
% 3.32/1.03  --comb_inst_mult                        10
% 3.32/1.03  
% 3.32/1.03  ------ Debug Options
% 3.32/1.03  
% 3.32/1.03  --dbg_backtrace                         false
% 3.32/1.03  --dbg_dump_prop_clauses                 false
% 3.32/1.03  --dbg_dump_prop_clauses_file            -
% 3.32/1.03  --dbg_out_stat                          false
% 3.32/1.03  
% 3.32/1.03  
% 3.32/1.03  
% 3.32/1.03  
% 3.32/1.03  ------ Proving...
% 3.32/1.03  
% 3.32/1.03  
% 3.32/1.03  % SZS status Theorem for theBenchmark.p
% 3.32/1.03  
% 3.32/1.03   Resolution empty clause
% 3.32/1.03  
% 3.32/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/1.03  
% 3.32/1.03  fof(f17,axiom,(
% 3.32/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f42,plain,(
% 3.32/1.03    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/1.03    inference(ennf_transformation,[],[f17])).
% 3.32/1.03  
% 3.32/1.03  fof(f58,plain,(
% 3.32/1.03    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/1.03    inference(nnf_transformation,[],[f42])).
% 3.32/1.03  
% 3.32/1.03  fof(f96,plain,(
% 3.32/1.03    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/1.03    inference(cnf_transformation,[],[f58])).
% 3.32/1.03  
% 3.32/1.03  fof(f5,axiom,(
% 3.32/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f55,plain,(
% 3.32/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.32/1.03    inference(nnf_transformation,[],[f5])).
% 3.32/1.03  
% 3.32/1.03  fof(f80,plain,(
% 3.32/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f55])).
% 3.32/1.03  
% 3.32/1.03  fof(f22,conjecture,(
% 3.32/1.03    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f23,negated_conjecture,(
% 3.32/1.03    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.32/1.03    inference(negated_conjecture,[],[f22])).
% 3.32/1.03  
% 3.32/1.03  fof(f51,plain,(
% 3.32/1.03    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.32/1.03    inference(ennf_transformation,[],[f23])).
% 3.32/1.03  
% 3.32/1.03  fof(f52,plain,(
% 3.32/1.03    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.32/1.03    inference(flattening,[],[f51])).
% 3.32/1.03  
% 3.32/1.03  fof(f68,plain,(
% 3.32/1.03    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.32/1.03    inference(nnf_transformation,[],[f52])).
% 3.32/1.03  
% 3.32/1.03  fof(f69,plain,(
% 3.32/1.03    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.32/1.03    inference(flattening,[],[f68])).
% 3.32/1.03  
% 3.32/1.03  fof(f71,plain,(
% 3.32/1.03    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK3,u1_struct_0(X0)) | ~v3_tex_2(sK3,X0)) & (~v1_subset_1(sK3,u1_struct_0(X0)) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.32/1.03    introduced(choice_axiom,[])).
% 3.32/1.03  
% 3.32/1.03  fof(f70,plain,(
% 3.32/1.03    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.32/1.03    introduced(choice_axiom,[])).
% 3.32/1.03  
% 3.32/1.03  fof(f72,plain,(
% 3.32/1.03    ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.32/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f69,f71,f70])).
% 3.32/1.03  
% 3.32/1.03  fof(f113,plain,(
% 3.32/1.03    ~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)),
% 3.32/1.03    inference(cnf_transformation,[],[f72])).
% 3.32/1.03  
% 3.32/1.03  fof(f112,plain,(
% 3.32/1.03    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.32/1.03    inference(cnf_transformation,[],[f72])).
% 3.32/1.03  
% 3.32/1.03  fof(f79,plain,(
% 3.32/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.32/1.03    inference(cnf_transformation,[],[f55])).
% 3.32/1.03  
% 3.32/1.03  fof(f95,plain,(
% 3.32/1.03    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/1.03    inference(cnf_transformation,[],[f58])).
% 3.32/1.03  
% 3.32/1.03  fof(f115,plain,(
% 3.32/1.03    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.32/1.03    inference(equality_resolution,[],[f95])).
% 3.32/1.03  
% 3.32/1.03  fof(f114,plain,(
% 3.32/1.03    v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)),
% 3.32/1.03    inference(cnf_transformation,[],[f72])).
% 3.32/1.03  
% 3.32/1.03  fof(f111,plain,(
% 3.32/1.03    l1_pre_topc(sK2)),
% 3.32/1.03    inference(cnf_transformation,[],[f72])).
% 3.32/1.03  
% 3.32/1.03  fof(f7,axiom,(
% 3.32/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f29,plain,(
% 3.32/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f7])).
% 3.32/1.03  
% 3.32/1.03  fof(f82,plain,(
% 3.32/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f29])).
% 3.32/1.03  
% 3.32/1.03  fof(f6,axiom,(
% 3.32/1.03    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f28,plain,(
% 3.32/1.03    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f6])).
% 3.32/1.03  
% 3.32/1.03  fof(f81,plain,(
% 3.32/1.03    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f28])).
% 3.32/1.03  
% 3.32/1.03  fof(f8,axiom,(
% 3.32/1.03    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f30,plain,(
% 3.32/1.03    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f8])).
% 3.32/1.03  
% 3.32/1.03  fof(f83,plain,(
% 3.32/1.03    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f30])).
% 3.32/1.03  
% 3.32/1.03  fof(f1,axiom,(
% 3.32/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f24,plain,(
% 3.32/1.03    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/1.03    inference(ennf_transformation,[],[f1])).
% 3.32/1.03  
% 3.32/1.03  fof(f73,plain,(
% 3.32/1.03    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/1.03    inference(cnf_transformation,[],[f24])).
% 3.32/1.03  
% 3.32/1.03  fof(f2,axiom,(
% 3.32/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f25,plain,(
% 3.32/1.03    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/1.03    inference(ennf_transformation,[],[f2])).
% 3.32/1.03  
% 3.32/1.03  fof(f53,plain,(
% 3.32/1.03    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/1.03    inference(nnf_transformation,[],[f25])).
% 3.32/1.03  
% 3.32/1.03  fof(f75,plain,(
% 3.32/1.03    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/1.03    inference(cnf_transformation,[],[f53])).
% 3.32/1.03  
% 3.32/1.03  fof(f9,axiom,(
% 3.32/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f31,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f9])).
% 3.32/1.03  
% 3.32/1.03  fof(f84,plain,(
% 3.32/1.03    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f31])).
% 3.32/1.03  
% 3.32/1.03  fof(f3,axiom,(
% 3.32/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f26,plain,(
% 3.32/1.03    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.32/1.03    inference(ennf_transformation,[],[f3])).
% 3.32/1.03  
% 3.32/1.03  fof(f76,plain,(
% 3.32/1.03    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.32/1.03    inference(cnf_transformation,[],[f26])).
% 3.32/1.03  
% 3.32/1.03  fof(f18,axiom,(
% 3.32/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f43,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f18])).
% 3.32/1.03  
% 3.32/1.03  fof(f44,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(flattening,[],[f43])).
% 3.32/1.03  
% 3.32/1.03  fof(f59,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(nnf_transformation,[],[f44])).
% 3.32/1.03  
% 3.32/1.03  fof(f60,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(flattening,[],[f59])).
% 3.32/1.03  
% 3.32/1.03  fof(f61,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(rectify,[],[f60])).
% 3.32/1.03  
% 3.32/1.03  fof(f62,plain,(
% 3.32/1.03    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.32/1.03    introduced(choice_axiom,[])).
% 3.32/1.03  
% 3.32/1.03  fof(f63,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f61,f62])).
% 3.32/1.03  
% 3.32/1.03  fof(f98,plain,(
% 3.32/1.03    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f63])).
% 3.32/1.03  
% 3.32/1.03  fof(f20,axiom,(
% 3.32/1.03    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f47,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.32/1.03    inference(ennf_transformation,[],[f20])).
% 3.32/1.03  
% 3.32/1.03  fof(f48,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.32/1.03    inference(flattening,[],[f47])).
% 3.32/1.03  
% 3.32/1.03  fof(f106,plain,(
% 3.32/1.03    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f48])).
% 3.32/1.03  
% 3.32/1.03  fof(f108,plain,(
% 3.32/1.03    ~v2_struct_0(sK2)),
% 3.32/1.03    inference(cnf_transformation,[],[f72])).
% 3.32/1.03  
% 3.32/1.03  fof(f109,plain,(
% 3.32/1.03    v2_pre_topc(sK2)),
% 3.32/1.03    inference(cnf_transformation,[],[f72])).
% 3.32/1.03  
% 3.32/1.03  fof(f110,plain,(
% 3.32/1.03    v1_tdlat_3(sK2)),
% 3.32/1.03    inference(cnf_transformation,[],[f72])).
% 3.32/1.03  
% 3.32/1.03  fof(f14,axiom,(
% 3.32/1.03    ! [X0] : (l1_pre_topc(X0) => v1_tops_1(k2_struct_0(X0),X0))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f38,plain,(
% 3.32/1.03    ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f14])).
% 3.32/1.03  
% 3.32/1.03  fof(f91,plain,(
% 3.32/1.03    ( ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f38])).
% 3.32/1.03  
% 3.32/1.03  fof(f21,axiom,(
% 3.32/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f49,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.32/1.03    inference(ennf_transformation,[],[f21])).
% 3.32/1.03  
% 3.32/1.03  fof(f50,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.32/1.03    inference(flattening,[],[f49])).
% 3.32/1.03  
% 3.32/1.03  fof(f107,plain,(
% 3.32/1.03    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f50])).
% 3.32/1.03  
% 3.32/1.03  fof(f16,axiom,(
% 3.32/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f41,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f16])).
% 3.32/1.03  
% 3.32/1.03  fof(f57,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(nnf_transformation,[],[f41])).
% 3.32/1.03  
% 3.32/1.03  fof(f94,plain,(
% 3.32/1.03    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f57])).
% 3.32/1.03  
% 3.32/1.03  fof(f93,plain,(
% 3.32/1.03    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f57])).
% 3.32/1.03  
% 3.32/1.03  fof(f15,axiom,(
% 3.32/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 3.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.03  
% 3.32/1.03  fof(f39,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(ennf_transformation,[],[f15])).
% 3.32/1.03  
% 3.32/1.03  fof(f40,plain,(
% 3.32/1.03    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.32/1.03    inference(flattening,[],[f39])).
% 3.32/1.03  
% 3.32/1.03  fof(f92,plain,(
% 3.32/1.03    ( ! [X2,X0,X1] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.32/1.03    inference(cnf_transformation,[],[f40])).
% 3.32/1.03  
% 3.32/1.03  cnf(c_22,plain,
% 3.32/1.03      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 3.32/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_6,plain,
% 3.32/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_324,plain,
% 3.32/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.32/1.03      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_412,plain,
% 3.32/1.03      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 3.32/1.03      inference(bin_hyper_res,[status(thm)],[c_22,c_324]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_36,negated_conjecture,
% 3.32/1.03      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f113]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_326,plain,
% 3.32/1.03      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.32/1.03      inference(prop_impl,[status(thm)],[c_36]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_741,plain,
% 3.32/1.03      ( v3_tex_2(sK3,sK2)
% 3.32/1.03      | ~ r1_tarski(X0,X1)
% 3.32/1.03      | X1 = X0
% 3.32/1.03      | u1_struct_0(sK2) != X1
% 3.32/1.03      | sK3 != X0 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_412,c_326]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_742,plain,
% 3.32/1.03      ( v3_tex_2(sK3,sK2)
% 3.32/1.03      | ~ r1_tarski(sK3,u1_struct_0(sK2))
% 3.32/1.03      | u1_struct_0(sK2) = sK3 ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_741]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2784,plain,
% 3.32/1.03      ( u1_struct_0(sK2) = sK3
% 3.32/1.03      | v3_tex_2(sK3,sK2) = iProver_top
% 3.32/1.03      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_37,negated_conjecture,
% 3.32/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(cnf_transformation,[],[f112]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_46,plain,
% 3.32/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_743,plain,
% 3.32/1.03      ( u1_struct_0(sK2) = sK3
% 3.32/1.03      | v3_tex_2(sK3,sK2) = iProver_top
% 3.32/1.03      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_7,plain,
% 3.32/1.03      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3083,plain,
% 3.32/1.03      ( r1_tarski(sK3,u1_struct_0(sK2))
% 3.32/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3084,plain,
% 3.32/1.03      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
% 3.32/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_3083]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_23,plain,
% 3.32/1.03      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f115]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_35,negated_conjecture,
% 3.32/1.03      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f114]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_328,plain,
% 3.32/1.03      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.32/1.03      inference(prop_impl,[status(thm)],[c_35]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_754,plain,
% 3.32/1.03      ( ~ v3_tex_2(sK3,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.32/1.03      | u1_struct_0(sK2) != X0
% 3.32/1.03      | sK3 != X0 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_328]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_755,plain,
% 3.32/1.03      ( ~ v3_tex_2(sK3,sK2)
% 3.32/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | sK3 != u1_struct_0(sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_754]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2783,plain,
% 3.32/1.03      ( sK3 != u1_struct_0(sK2)
% 3.32/1.03      | v3_tex_2(sK3,sK2) != iProver_top
% 3.32/1.03      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_38,negated_conjecture,
% 3.32/1.03      ( l1_pre_topc(sK2) ),
% 3.32/1.03      inference(cnf_transformation,[],[f111]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_45,plain,
% 3.32/1.03      ( l1_pre_topc(sK2) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_9,plain,
% 3.32/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.32/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_118,plain,
% 3.32/1.03      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_120,plain,
% 3.32/1.03      ( l1_pre_topc(sK2) != iProver_top | l1_struct_0(sK2) = iProver_top ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_118]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_8,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.32/1.03      | ~ l1_struct_0(X0) ),
% 3.32/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_121,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.32/1.03      | l1_struct_0(X0) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_123,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.32/1.03      | l1_struct_0(sK2) != iProver_top ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_121]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_10,plain,
% 3.32/1.03      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 3.32/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_722,plain,
% 3.32/1.03      ( ~ v3_tex_2(sK3,sK2)
% 3.32/1.03      | ~ l1_struct_0(X0)
% 3.32/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.32/1.03      | k2_struct_0(X0) != sK3 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_328]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_723,plain,
% 3.32/1.03      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 3.32/1.03      | k2_struct_0(X0) != sK3
% 3.32/1.03      | v3_tex_2(sK3,sK2) != iProver_top
% 3.32/1.03      | l1_struct_0(X0) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_725,plain,
% 3.32/1.03      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.32/1.03      | k2_struct_0(sK2) != sK3
% 3.32/1.03      | v3_tex_2(sK3,sK2) != iProver_top
% 3.32/1.03      | l1_struct_0(sK2) != iProver_top ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_723]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2148,plain,
% 3.32/1.03      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.32/1.03      theory(equality) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2160,plain,
% 3.32/1.03      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_2148]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2140,plain,( X0 = X0 ),theory(equality) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2167,plain,
% 3.32/1.03      ( sK2 = sK2 ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_2140]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_0,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/1.03      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_407,plain,
% 3.32/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.32/1.03      inference(bin_hyper_res,[status(thm)],[c_0,c_324]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3175,plain,
% 3.32/1.03      ( ~ r1_tarski(sK3,u1_struct_0(sK2))
% 3.32/1.03      | m1_subset_1(k3_subset_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_407]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3177,plain,
% 3.32/1.03      ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
% 3.32/1.03      | m1_subset_1(k3_subset_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_3175]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1,plain,
% 3.32/1.03      ( r1_tarski(X0,X1)
% 3.32/1.03      | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 3.32/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3109,plain,
% 3.32/1.03      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK2),X0),k3_subset_1(u1_struct_0(sK2),sK3))
% 3.32/1.03      | r1_tarski(sK3,X0)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3196,plain,
% 3.32/1.03      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK2),k2_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK3))
% 3.32/1.03      | r1_tarski(sK3,k2_struct_0(sK2))
% 3.32/1.03      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_3109]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3197,plain,
% 3.32/1.03      ( r1_tarski(k3_subset_1(u1_struct_0(sK2),k2_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK3)) != iProver_top
% 3.32/1.03      | r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top
% 3.32/1.03      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.32/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_3196]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2788,plain,
% 3.32/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_11,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ l1_struct_0(X1)
% 3.32/1.03      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 3.32/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_841,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ l1_pre_topc(X2)
% 3.32/1.03      | X1 != X2
% 3.32/1.03      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_842,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ l1_pre_topc(X1)
% 3.32/1.03      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_841]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_983,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
% 3.32/1.03      | sK2 != X1 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_842,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_984,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | k4_subset_1(u1_struct_0(sK2),X0,k3_subset_1(u1_struct_0(sK2),X0)) = k2_struct_0(sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_983]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2779,plain,
% 3.32/1.03      ( k4_subset_1(u1_struct_0(sK2),X0,k3_subset_1(u1_struct_0(sK2),X0)) = k2_struct_0(sK2)
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3102,plain,
% 3.32/1.03      ( k4_subset_1(u1_struct_0(sK2),sK3,k3_subset_1(u1_struct_0(sK2),sK3)) = k2_struct_0(sK2) ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2788,c_2779]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3,plain,
% 3.32/1.03      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
% 3.32/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.32/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 3.32/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2791,plain,
% 3.32/1.03      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) = iProver_top
% 3.32/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.32/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3270,plain,
% 3.32/1.03      ( r1_tarski(k3_subset_1(u1_struct_0(sK2),k2_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK3)) = iProver_top
% 3.32/1.03      | m1_subset_1(k3_subset_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.32/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_3102,c_2791]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_815,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.32/1.03      | ~ l1_pre_topc(X0) ),
% 3.32/1.03      inference(resolution,[status(thm)],[c_9,c_8]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_946,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK2 != X0 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_815,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_947,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_946]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2782,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_28,plain,
% 3.32/1.03      ( ~ v2_tex_2(X0,X1)
% 3.32/1.03      | ~ v3_tex_2(X2,X1)
% 3.32/1.03      | ~ r1_tarski(X2,X0)
% 3.32/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ l1_pre_topc(X1)
% 3.32/1.03      | X0 = X2 ),
% 3.32/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1016,plain,
% 3.32/1.03      ( ~ v2_tex_2(X0,X1)
% 3.32/1.03      | ~ v3_tex_2(X2,X1)
% 3.32/1.03      | ~ r1_tarski(X2,X0)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | X2 = X0
% 3.32/1.03      | sK2 != X1 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1017,plain,
% 3.32/1.03      ( ~ v2_tex_2(X0,sK2)
% 3.32/1.03      | ~ v3_tex_2(X1,sK2)
% 3.32/1.03      | ~ r1_tarski(X1,X0)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | X1 = X0 ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_1016]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_33,plain,
% 3.32/1.03      ( v2_tex_2(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | v2_struct_0(X1)
% 3.32/1.03      | ~ v1_tdlat_3(X1)
% 3.32/1.03      | ~ v2_pre_topc(X1)
% 3.32/1.03      | ~ l1_pre_topc(X1) ),
% 3.32/1.03      inference(cnf_transformation,[],[f106]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_41,negated_conjecture,
% 3.32/1.03      ( ~ v2_struct_0(sK2) ),
% 3.32/1.03      inference(cnf_transformation,[],[f108]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_590,plain,
% 3.32/1.03      ( v2_tex_2(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ v1_tdlat_3(X1)
% 3.32/1.03      | ~ v2_pre_topc(X1)
% 3.32/1.03      | ~ l1_pre_topc(X1)
% 3.32/1.03      | sK2 != X1 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_33,c_41]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_591,plain,
% 3.32/1.03      ( v2_tex_2(X0,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ v1_tdlat_3(sK2)
% 3.32/1.03      | ~ v2_pre_topc(sK2)
% 3.32/1.03      | ~ l1_pre_topc(sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_590]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_40,negated_conjecture,
% 3.32/1.03      ( v2_pre_topc(sK2) ),
% 3.32/1.03      inference(cnf_transformation,[],[f109]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_39,negated_conjecture,
% 3.32/1.03      ( v1_tdlat_3(sK2) ),
% 3.32/1.03      inference(cnf_transformation,[],[f110]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_595,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tex_2(X0,sK2) ),
% 3.32/1.03      inference(global_propositional_subsumption,
% 3.32/1.03                [status(thm)],
% 3.32/1.03                [c_591,c_40,c_39,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_596,plain,
% 3.32/1.03      ( v2_tex_2(X0,sK2) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(renaming,[status(thm)],[c_595]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1021,plain,
% 3.32/1.03      ( ~ v3_tex_2(X1,sK2)
% 3.32/1.03      | ~ r1_tarski(X1,X0)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | X1 = X0 ),
% 3.32/1.03      inference(global_propositional_subsumption,
% 3.32/1.03                [status(thm)],
% 3.32/1.03                [c_1017,c_40,c_39,c_38,c_591]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1022,plain,
% 3.32/1.03      ( ~ v3_tex_2(X0,sK2)
% 3.32/1.03      | ~ r1_tarski(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | X0 = X1 ),
% 3.32/1.03      inference(renaming,[status(thm)],[c_1021]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2777,plain,
% 3.32/1.03      ( X0 = X1
% 3.32/1.03      | v3_tex_2(X0,sK2) != iProver_top
% 3.32/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.32/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_4182,plain,
% 3.32/1.03      ( sK3 = X0
% 3.32/1.03      | v3_tex_2(sK3,sK2) != iProver_top
% 3.32/1.03      | r1_tarski(sK3,X0) != iProver_top
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2788,c_2777]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_4238,plain,
% 3.32/1.03      ( k2_struct_0(sK2) = sK3
% 3.32/1.03      | v3_tex_2(sK3,sK2) != iProver_top
% 3.32/1.03      | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2782,c_4182]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_5235,plain,
% 3.32/1.03      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 3.32/1.03      inference(global_propositional_subsumption,
% 3.32/1.03                [status(thm)],
% 3.32/1.03                [c_2783,c_45,c_46,c_120,c_123,c_725,c_2160,c_2167,c_3084,
% 3.32/1.03                 c_3177,c_3197,c_3270,c_4238]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_5677,plain,
% 3.32/1.03      ( u1_struct_0(sK2) = sK3 ),
% 3.32/1.03      inference(global_propositional_subsumption,
% 3.32/1.03                [status(thm)],
% 3.32/1.03                [c_2784,c_45,c_46,c_120,c_123,c_725,c_743,c_2160,c_2167,
% 3.32/1.03                 c_3084,c_3177,c_3197,c_3270,c_4238]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2789,plain,
% 3.32/1.03      ( r1_tarski(X0,X1) = iProver_top
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3166,plain,
% 3.32/1.03      ( r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2782,c_2789]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_707,plain,
% 3.32/1.03      ( ~ r1_tarski(X0,X1)
% 3.32/1.03      | ~ l1_struct_0(X2)
% 3.32/1.03      | X1 = X0
% 3.32/1.03      | u1_struct_0(X2) != X1
% 3.32/1.03      | k2_struct_0(X2) != X0 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_412]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_708,plain,
% 3.32/1.03      ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
% 3.32/1.03      | ~ l1_struct_0(X0)
% 3.32/1.03      | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_707]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_801,plain,
% 3.32/1.03      ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
% 3.32/1.03      | ~ l1_pre_topc(X0)
% 3.32/1.03      | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.32/1.03      inference(resolution,[status(thm)],[c_9,c_708]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_953,plain,
% 3.32/1.03      ( ~ r1_tarski(k2_struct_0(X0),u1_struct_0(X0))
% 3.32/1.03      | u1_struct_0(X0) = k2_struct_0(X0)
% 3.32/1.03      | sK2 != X0 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_801,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_954,plain,
% 3.32/1.03      ( ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
% 3.32/1.03      | u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_953]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2781,plain,
% 3.32/1.03      ( u1_struct_0(sK2) = k2_struct_0(sK2)
% 3.32/1.03      | r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3887,plain,
% 3.32/1.03      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_3166,c_2781]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_5680,plain,
% 3.32/1.03      ( k2_struct_0(sK2) = sK3 ),
% 3.32/1.03      inference(demodulation,[status(thm)],[c_5677,c_3887]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_18,plain,
% 3.32/1.03      ( v1_tops_1(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) ),
% 3.32/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_976,plain,
% 3.32/1.03      ( v1_tops_1(k2_struct_0(X0),X0) | sK2 != X0 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_977,plain,
% 3.32/1.03      ( v1_tops_1(k2_struct_0(sK2),sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_976]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2780,plain,
% 3.32/1.03      ( v1_tops_1(k2_struct_0(sK2),sK2) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2790,plain,
% 3.32/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_34,plain,
% 3.32/1.03      ( ~ v2_tex_2(X0,X1)
% 3.32/1.03      | v3_tex_2(X0,X1)
% 3.32/1.03      | ~ v1_tops_1(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | v2_struct_0(X1)
% 3.32/1.03      | ~ v2_pre_topc(X1)
% 3.32/1.03      | ~ l1_pre_topc(X1) ),
% 3.32/1.03      inference(cnf_transformation,[],[f107]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_566,plain,
% 3.32/1.03      ( ~ v2_tex_2(X0,X1)
% 3.32/1.03      | v3_tex_2(X0,X1)
% 3.32/1.03      | ~ v1_tops_1(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ v2_pre_topc(X1)
% 3.32/1.03      | ~ l1_pre_topc(X1)
% 3.32/1.03      | sK2 != X1 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_34,c_41]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_567,plain,
% 3.32/1.03      ( ~ v2_tex_2(X0,sK2)
% 3.32/1.03      | v3_tex_2(X0,sK2)
% 3.32/1.03      | ~ v1_tops_1(X0,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ v2_pre_topc(sK2)
% 3.32/1.03      | ~ l1_pre_topc(sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_566]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_571,plain,
% 3.32/1.03      ( ~ v2_tex_2(X0,sK2)
% 3.32/1.03      | v3_tex_2(X0,sK2)
% 3.32/1.03      | ~ v1_tops_1(X0,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(global_propositional_subsumption,
% 3.32/1.03                [status(thm)],
% 3.32/1.03                [c_567,c_40,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_606,plain,
% 3.32/1.03      ( v3_tex_2(X0,sK2)
% 3.32/1.03      | ~ v1_tops_1(X0,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(backward_subsumption_resolution,[status(thm)],[c_596,c_571]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2786,plain,
% 3.32/1.03      ( v3_tex_2(X0,sK2) = iProver_top
% 3.32/1.03      | v1_tops_1(X0,sK2) != iProver_top
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_6085,plain,
% 3.32/1.03      ( v3_tex_2(X0,sK2) = iProver_top
% 3.32/1.03      | v1_tops_1(X0,sK2) != iProver_top
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top ),
% 3.32/1.03      inference(light_normalisation,[status(thm)],[c_2786,c_5677]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_6092,plain,
% 3.32/1.03      ( v3_tex_2(X0,sK2) = iProver_top
% 3.32/1.03      | v1_tops_1(X0,sK2) != iProver_top
% 3.32/1.03      | r1_tarski(X0,sK3) != iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2790,c_6085]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_6601,plain,
% 3.32/1.03      ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
% 3.32/1.03      | r1_tarski(k2_struct_0(sK2),sK3) != iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2780,c_6092]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_91,plain,
% 3.32/1.03      ( v1_tops_1(k2_struct_0(X0),X0) = iProver_top
% 3.32/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_93,plain,
% 3.32/1.03      ( v1_tops_1(k2_struct_0(sK2),sK2) = iProver_top
% 3.32/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_91]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_119,plain,
% 3.32/1.03      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_122,plain,
% 3.32/1.03      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ l1_struct_0(sK2) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_710,plain,
% 3.32/1.03      ( ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
% 3.32/1.03      | ~ l1_struct_0(sK2)
% 3.32/1.03      | u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_708]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1557,plain,
% 3.32/1.03      ( ~ v1_tops_1(X0,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | u1_struct_0(sK2) != sK3
% 3.32/1.03      | sK2 != sK2
% 3.32/1.03      | sK3 != X0 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_755,c_606]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1558,plain,
% 3.32/1.03      ( ~ v1_tops_1(sK3,sK2)
% 3.32/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | u1_struct_0(sK2) != sK3 ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_1557]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_20,plain,
% 3.32/1.03      ( v1_tops_1(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ l1_pre_topc(X1)
% 3.32/1.03      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 3.32/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1142,plain,
% 3.32/1.03      ( v1_tops_1(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 3.32/1.03      | sK2 != X1 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1143,plain,
% 3.32/1.03      ( v1_tops_1(X0,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_1142]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3027,plain,
% 3.32/1.03      ( v1_tops_1(sK3,sK2)
% 3.32/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | k2_pre_topc(sK2,sK3) != u1_struct_0(sK2) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_1143]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3086,plain,
% 3.32/1.03      ( r1_tarski(k2_struct_0(sK2),u1_struct_0(sK2))
% 3.32/1.03      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3415,plain,
% 3.32/1.03      ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_2140]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_21,plain,
% 3.32/1.03      ( ~ v1_tops_1(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ l1_pre_topc(X1)
% 3.32/1.03      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.32/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1127,plain,
% 3.32/1.03      ( ~ v1_tops_1(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 3.32/1.03      | sK2 != X1 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1128,plain,
% 3.32/1.03      ( ~ v1_tops_1(X0,sK2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_1127]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2773,plain,
% 3.32/1.03      ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 3.32/1.03      | v1_tops_1(X0,sK2) != iProver_top
% 3.32/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3586,plain,
% 3.32/1.03      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
% 3.32/1.03      | v1_tops_1(sK3,sK2) != iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2788,c_2773]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_19,plain,
% 3.32/1.03      ( ~ v1_tops_1(X0,X1)
% 3.32/1.03      | v1_tops_1(X2,X1)
% 3.32/1.03      | ~ r1_tarski(X0,X2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ l1_pre_topc(X1) ),
% 3.32/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1157,plain,
% 3.32/1.03      ( ~ v1_tops_1(X0,X1)
% 3.32/1.03      | v1_tops_1(X2,X1)
% 3.32/1.03      | ~ r1_tarski(X0,X2)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.32/1.03      | sK2 != X1 ),
% 3.32/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_1158,plain,
% 3.32/1.03      ( ~ v1_tops_1(X0,sK2)
% 3.32/1.03      | v1_tops_1(X1,sK2)
% 3.32/1.03      | ~ r1_tarski(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(unflattening,[status(thm)],[c_1157]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3054,plain,
% 3.32/1.03      ( v1_tops_1(X0,sK2)
% 3.32/1.03      | ~ v1_tops_1(k2_struct_0(sK2),sK2)
% 3.32/1.03      | ~ r1_tarski(k2_struct_0(sK2),X0)
% 3.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_1158]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3647,plain,
% 3.32/1.03      ( ~ v1_tops_1(k2_struct_0(sK2),sK2)
% 3.32/1.03      | v1_tops_1(sK3,sK2)
% 3.32/1.03      | ~ r1_tarski(k2_struct_0(sK2),sK3)
% 3.32/1.03      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_3054]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3648,plain,
% 3.32/1.03      ( v1_tops_1(k2_struct_0(sK2),sK2) != iProver_top
% 3.32/1.03      | v1_tops_1(sK3,sK2) = iProver_top
% 3.32/1.03      | r1_tarski(k2_struct_0(sK2),sK3) != iProver_top
% 3.32/1.03      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.32/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.32/1.03      inference(predicate_to_equality,[status(thm)],[c_3647]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_2144,plain,
% 3.32/1.03      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.32/1.03      theory(equality) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3094,plain,
% 3.32/1.03      ( m1_subset_1(X0,X1)
% 3.32/1.03      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | X0 != k2_struct_0(sK2)
% 3.32/1.03      | X1 != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_2144]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3484,plain,
% 3.32/1.03      ( m1_subset_1(u1_struct_0(sK2),X0)
% 3.32/1.03      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | X0 != k1_zfmisc_1(u1_struct_0(sK2))
% 3.32/1.03      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_3094]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_4535,plain,
% 3.32/1.03      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.32/1.03      | u1_struct_0(sK2) != k2_struct_0(sK2)
% 3.32/1.03      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.32/1.03      inference(instantiation,[status(thm)],[c_3484]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_7205,plain,
% 3.32/1.03      ( r1_tarski(k2_struct_0(sK2),sK3) != iProver_top ),
% 3.32/1.03      inference(global_propositional_subsumption,
% 3.32/1.03                [status(thm)],
% 3.32/1.03                [c_6601,c_38,c_45,c_37,c_46,c_93,c_119,c_120,c_122,c_123,
% 3.32/1.03                 c_710,c_725,c_743,c_1558,c_2160,c_2167,c_3027,c_3084,c_3086,
% 3.32/1.03                 c_3177,c_3197,c_3270,c_3415,c_3586,c_3648,c_4238,c_4535]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_10538,plain,
% 3.32/1.03      ( r1_tarski(sK3,sK3) != iProver_top ),
% 3.32/1.03      inference(demodulation,[status(thm)],[c_5680,c_7205]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_3165,plain,
% 3.32/1.03      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.32/1.03      inference(superposition,[status(thm)],[c_2788,c_2789]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_4824,plain,
% 3.32/1.03      ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top ),
% 3.32/1.03      inference(demodulation,[status(thm)],[c_3887,c_3165]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_10555,plain,
% 3.32/1.03      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.32/1.03      inference(demodulation,[status(thm)],[c_5680,c_4824]) ).
% 3.32/1.03  
% 3.32/1.03  cnf(c_10626,plain,
% 3.32/1.03      ( $false ),
% 3.32/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_10538,c_10555]) ).
% 3.32/1.03  
% 3.32/1.03  
% 3.32/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/1.03  
% 3.32/1.03  ------                               Statistics
% 3.32/1.03  
% 3.32/1.03  ------ General
% 3.32/1.03  
% 3.32/1.03  abstr_ref_over_cycles:                  0
% 3.32/1.03  abstr_ref_under_cycles:                 0
% 3.32/1.03  gc_basic_clause_elim:                   0
% 3.32/1.03  forced_gc_time:                         0
% 3.32/1.03  parsing_time:                           0.026
% 3.32/1.03  unif_index_cands_time:                  0.
% 3.32/1.03  unif_index_add_time:                    0.
% 3.32/1.03  orderings_time:                         0.
% 3.32/1.03  out_proof_time:                         0.013
% 3.32/1.03  total_time:                             0.428
% 3.32/1.03  num_of_symbols:                         55
% 3.32/1.03  num_of_terms:                           9192
% 3.32/1.03  
% 3.32/1.03  ------ Preprocessing
% 3.32/1.03  
% 3.32/1.03  num_of_splits:                          0
% 3.32/1.03  num_of_split_atoms:                     0
% 3.32/1.03  num_of_reused_defs:                     0
% 3.32/1.03  num_eq_ax_congr_red:                    15
% 3.32/1.03  num_of_sem_filtered_clauses:            1
% 3.32/1.03  num_of_subtypes:                        0
% 3.32/1.03  monotx_restored_types:                  0
% 3.32/1.03  sat_num_of_epr_types:                   0
% 3.32/1.03  sat_num_of_non_cyclic_types:            0
% 3.32/1.03  sat_guarded_non_collapsed_types:        0
% 3.32/1.03  num_pure_diseq_elim:                    0
% 3.32/1.03  simp_replaced_by:                       0
% 3.32/1.03  res_preprocessed:                       152
% 3.32/1.03  prep_upred:                             0
% 3.32/1.03  prep_unflattend:                        60
% 3.32/1.03  smt_new_axioms:                         0
% 3.32/1.03  pred_elim_cands:                        4
% 3.32/1.03  pred_elim:                              9
% 3.32/1.03  pred_elim_cl:                           15
% 3.32/1.03  pred_elim_cycles:                       13
% 3.32/1.03  merged_defs:                            10
% 3.32/1.03  merged_defs_ncl:                        0
% 3.32/1.03  bin_hyper_res:                          14
% 3.32/1.03  prep_cycles:                            4
% 3.32/1.03  pred_elim_time:                         0.024
% 3.32/1.03  splitting_time:                         0.
% 3.32/1.03  sem_filter_time:                        0.
% 3.32/1.03  monotx_time:                            0.
% 3.32/1.03  subtype_inf_time:                       0.
% 3.32/1.03  
% 3.32/1.03  ------ Problem properties
% 3.32/1.03  
% 3.32/1.03  clauses:                                27
% 3.32/1.03  conjectures:                            1
% 3.32/1.03  epr:                                    0
% 3.32/1.03  horn:                                   24
% 3.32/1.03  ground:                                 7
% 3.32/1.03  unary:                                  3
% 3.32/1.03  binary:                                 8
% 3.32/1.03  lits:                                   77
% 3.32/1.03  lits_eq:                                15
% 3.32/1.03  fd_pure:                                0
% 3.32/1.03  fd_pseudo:                              0
% 3.32/1.03  fd_cond:                                0
% 3.32/1.03  fd_pseudo_cond:                         1
% 3.32/1.03  ac_symbols:                             0
% 3.32/1.03  
% 3.32/1.03  ------ Propositional Solver
% 3.32/1.03  
% 3.32/1.03  prop_solver_calls:                      27
% 3.32/1.03  prop_fast_solver_calls:                 1689
% 3.32/1.03  smt_solver_calls:                       0
% 3.32/1.03  smt_fast_solver_calls:                  0
% 3.32/1.03  prop_num_of_clauses:                    4209
% 3.32/1.03  prop_preprocess_simplified:             9675
% 3.32/1.03  prop_fo_subsumed:                       75
% 3.32/1.03  prop_solver_time:                       0.
% 3.32/1.03  smt_solver_time:                        0.
% 3.32/1.03  smt_fast_solver_time:                   0.
% 3.32/1.03  prop_fast_solver_time:                  0.
% 3.32/1.03  prop_unsat_core_time:                   0.
% 3.32/1.03  
% 3.32/1.03  ------ QBF
% 3.32/1.03  
% 3.32/1.03  qbf_q_res:                              0
% 3.32/1.03  qbf_num_tautologies:                    0
% 3.32/1.03  qbf_prep_cycles:                        0
% 3.32/1.03  
% 3.32/1.03  ------ BMC1
% 3.32/1.03  
% 3.32/1.03  bmc1_current_bound:                     -1
% 3.32/1.03  bmc1_last_solved_bound:                 -1
% 3.32/1.03  bmc1_unsat_core_size:                   -1
% 3.32/1.03  bmc1_unsat_core_parents_size:           -1
% 3.32/1.03  bmc1_merge_next_fun:                    0
% 3.32/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.32/1.03  
% 3.32/1.03  ------ Instantiation
% 3.32/1.03  
% 3.32/1.03  inst_num_of_clauses:                    1280
% 3.32/1.03  inst_num_in_passive:                    256
% 3.32/1.03  inst_num_in_active:                     460
% 3.32/1.03  inst_num_in_unprocessed:                564
% 3.32/1.03  inst_num_of_loops:                      490
% 3.32/1.03  inst_num_of_learning_restarts:          0
% 3.32/1.03  inst_num_moves_active_passive:          28
% 3.32/1.03  inst_lit_activity:                      0
% 3.32/1.03  inst_lit_activity_moves:                0
% 3.32/1.03  inst_num_tautologies:                   0
% 3.32/1.03  inst_num_prop_implied:                  0
% 3.32/1.03  inst_num_existing_simplified:           0
% 3.32/1.03  inst_num_eq_res_simplified:             0
% 3.32/1.03  inst_num_child_elim:                    0
% 3.32/1.03  inst_num_of_dismatching_blockings:      64
% 3.32/1.03  inst_num_of_non_proper_insts:           858
% 3.32/1.03  inst_num_of_duplicates:                 0
% 3.32/1.03  inst_inst_num_from_inst_to_res:         0
% 3.32/1.03  inst_dismatching_checking_time:         0.
% 3.32/1.03  
% 3.32/1.03  ------ Resolution
% 3.32/1.03  
% 3.32/1.03  res_num_of_clauses:                     0
% 3.32/1.03  res_num_in_passive:                     0
% 3.32/1.03  res_num_in_active:                      0
% 3.32/1.03  res_num_of_loops:                       156
% 3.32/1.03  res_forward_subset_subsumed:            49
% 3.32/1.03  res_backward_subset_subsumed:           0
% 3.32/1.03  res_forward_subsumed:                   1
% 3.32/1.03  res_backward_subsumed:                  0
% 3.32/1.03  res_forward_subsumption_resolution:     0
% 3.32/1.03  res_backward_subsumption_resolution:    1
% 3.32/1.03  res_clause_to_clause_subsumption:       667
% 3.32/1.03  res_orphan_elimination:                 0
% 3.32/1.03  res_tautology_del:                      55
% 3.32/1.03  res_num_eq_res_simplified:              1
% 3.32/1.03  res_num_sel_changes:                    0
% 3.32/1.03  res_moves_from_active_to_pass:          0
% 3.32/1.03  
% 3.32/1.03  ------ Superposition
% 3.32/1.03  
% 3.32/1.03  sup_time_total:                         0.
% 3.32/1.03  sup_time_generating:                    0.
% 3.32/1.03  sup_time_sim_full:                      0.
% 3.32/1.03  sup_time_sim_immed:                     0.
% 3.32/1.03  
% 3.32/1.03  sup_num_of_clauses:                     83
% 3.32/1.03  sup_num_in_active:                      29
% 3.32/1.03  sup_num_in_passive:                     54
% 3.32/1.03  sup_num_of_loops:                       96
% 3.32/1.03  sup_fw_superposition:                   127
% 3.32/1.03  sup_bw_superposition:                   50
% 3.32/1.03  sup_immediate_simplified:               24
% 3.32/1.03  sup_given_eliminated:                   0
% 3.32/1.03  comparisons_done:                       0
% 3.32/1.03  comparisons_avoided:                    0
% 3.32/1.03  
% 3.32/1.03  ------ Simplifications
% 3.32/1.03  
% 3.32/1.03  
% 3.32/1.03  sim_fw_subset_subsumed:                 18
% 3.32/1.03  sim_bw_subset_subsumed:                 2
% 3.32/1.03  sim_fw_subsumed:                        6
% 3.32/1.03  sim_bw_subsumed:                        0
% 3.32/1.03  sim_fw_subsumption_res:                 1
% 3.32/1.03  sim_bw_subsumption_res:                 0
% 3.32/1.03  sim_tautology_del:                      11
% 3.32/1.03  sim_eq_tautology_del:                   4
% 3.32/1.03  sim_eq_res_simp:                        1
% 3.32/1.03  sim_fw_demodulated:                     0
% 3.32/1.03  sim_bw_demodulated:                     66
% 3.32/1.03  sim_light_normalised:                   35
% 3.32/1.03  sim_joinable_taut:                      0
% 3.32/1.03  sim_joinable_simp:                      0
% 3.32/1.03  sim_ac_normalised:                      0
% 3.32/1.03  sim_smt_subsumption:                    0
% 3.32/1.03  
%------------------------------------------------------------------------------
