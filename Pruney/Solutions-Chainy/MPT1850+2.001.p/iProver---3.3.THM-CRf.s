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
% DateTime   : Thu Dec  3 12:25:29 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 391 expanded)
%              Number of clauses        :  118 ( 169 expanded)
%              Number of leaves         :   24 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  630 (1534 expanded)
%              Number of equality atoms :  169 ( 360 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v1_tdlat_3(sK1)
        & v1_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tdlat_3(X1)
            & v1_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ v1_tdlat_3(sK1)
    & v1_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f56,f55])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f80,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1213,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_12087,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2444,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10032,plain,
    ( ~ m1_pre_topc(sK0,X0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_2444])).

cnf(c_10034,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10032])).

cnf(c_11,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1237,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9537,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_13,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1329,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6618,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_6620,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6618])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1828,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),X0)
    | X0 = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2443,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))
    | u1_struct_0(X0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_5850,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4924,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_527,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1227,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_pre_topc(X3))
    | X2 != X0
    | u1_pre_topc(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_1297,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | r1_tarski(X2,u1_pre_topc(X1))
    | X2 != X0
    | u1_pre_topc(X1) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_1644,plain,
    ( r1_tarski(X0,u1_pre_topc(X1))
    | ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(X1))
    | X0 != k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(X1) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2950,plain,
    ( ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(X0))
    | r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
    | u1_pre_topc(X1) != k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(X0) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_4404,plain,
    ( ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(sK1))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2950])).

cnf(c_4406,plain,
    ( ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(sK1))
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | u1_pre_topc(sK0) != k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4404])).

cnf(c_537,plain,
    ( X0 != X1
    | k9_setfam_1(X0) = k9_setfam_1(X1) ),
    theory(equality)).

cnf(c_1432,plain,
    ( X0 != u1_struct_0(sK0)
    | k9_setfam_1(X0) = k9_setfam_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1837,plain,
    ( k9_setfam_1(u1_struct_0(X0)) = k9_setfam_1(u1_struct_0(sK0))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_4002,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) = k9_setfam_1(u1_struct_0(sK0))
    | u1_struct_0(sK1) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_966,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_175,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_4])).

cnf(c_176,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_959,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_973,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1879,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_973])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_30,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2055,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1879,c_30])).

cnf(c_2056,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2055])).

cnf(c_2063,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_2056])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_31,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2253,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_31])).

cnf(c_2254,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2253])).

cnf(c_2262,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_2254])).

cnf(c_3753,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_31])).

cnf(c_965,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_963,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1110,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_965,c_963])).

cnf(c_3758,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3753,c_1110])).

cnf(c_3779,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3758])).

cnf(c_3781,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3779])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2991,plain,
    ( ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_2993,plain,
    ( ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2991])).

cnf(c_526,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1204,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) != X0
    | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_2939,plain,
    ( k9_setfam_1(u1_struct_0(sK1)) != k9_setfam_1(u1_struct_0(sK0))
    | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_1429,plain,
    ( X0 != X1
    | X0 = k9_setfam_1(u1_struct_0(sK0))
    | k9_setfam_1(u1_struct_0(sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_1981,plain,
    ( X0 = k9_setfam_1(u1_struct_0(sK0))
    | X0 != u1_pre_topc(sK0)
    | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_2017,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_2938,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(sK1) = k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_14,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2422,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2283,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2262])).

cnf(c_1337,plain,
    ( v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),X0)
    | ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK0)
    | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2024,plain,
    ( ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK0)
    | v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_2019,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_1544,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_959])).

cnf(c_1629,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1544,c_30])).

cnf(c_1630,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1629])).

cnf(c_1878,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_973])).

cnf(c_1912,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1878])).

cnf(c_1914,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_1385,plain,
    ( ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),X0)
    | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1664,plain,
    ( ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_1250,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),X0)
    | u1_pre_topc(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1526,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
    | u1_pre_topc(sK1) = u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_1532,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1526])).

cnf(c_525,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1440,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_1421,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_531,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1258,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_1420,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1232,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | X1 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
    | X0 != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1315,plain,
    ( m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),X0)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | X0 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1363,plain,
    ( m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_1366,plain,
    ( m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_536,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1208,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(u1_pre_topc(X1),X1)
    | X0 != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1274,plain,
    ( v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK0)
    | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_542,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_23,plain,
    ( v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,negated_conjecture,
    ( ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_329,plain,
    ( ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_330,plain,
    ( ~ l1_pre_topc(sK1)
    | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_87,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_83,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_78,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_59,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_47,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_22,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_26,negated_conjecture,
    ( v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12087,c_10034,c_9537,c_6620,c_5850,c_4924,c_4406,c_4002,c_3781,c_2993,c_2939,c_2938,c_2422,c_2283,c_2024,c_2019,c_1914,c_1664,c_1532,c_1440,c_1421,c_1420,c_1366,c_1274,c_542,c_330,c_87,c_83,c_78,c_59,c_47,c_39,c_35,c_26,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 2.93/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.00  
% 2.93/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/1.00  
% 2.93/1.00  ------  iProver source info
% 2.93/1.00  
% 2.93/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.93/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/1.00  git: non_committed_changes: false
% 2.93/1.00  git: last_make_outside_of_git: false
% 2.93/1.00  
% 2.93/1.00  ------ 
% 2.93/1.00  
% 2.93/1.00  ------ Input Options
% 2.93/1.00  
% 2.93/1.00  --out_options                           all
% 2.93/1.00  --tptp_safe_out                         true
% 2.93/1.00  --problem_path                          ""
% 2.93/1.00  --include_path                          ""
% 2.93/1.00  --clausifier                            res/vclausify_rel
% 2.93/1.00  --clausifier_options                    --mode clausify
% 2.93/1.00  --stdin                                 false
% 2.93/1.00  --stats_out                             all
% 2.93/1.00  
% 2.93/1.00  ------ General Options
% 2.93/1.00  
% 2.93/1.00  --fof                                   false
% 2.93/1.00  --time_out_real                         305.
% 2.93/1.00  --time_out_virtual                      -1.
% 2.93/1.00  --symbol_type_check                     false
% 2.93/1.00  --clausify_out                          false
% 2.93/1.00  --sig_cnt_out                           false
% 2.93/1.00  --trig_cnt_out                          false
% 2.93/1.00  --trig_cnt_out_tolerance                1.
% 2.93/1.00  --trig_cnt_out_sk_spl                   false
% 2.93/1.00  --abstr_cl_out                          false
% 2.93/1.00  
% 2.93/1.00  ------ Global Options
% 2.93/1.00  
% 2.93/1.00  --schedule                              default
% 2.93/1.00  --add_important_lit                     false
% 2.93/1.00  --prop_solver_per_cl                    1000
% 2.93/1.00  --min_unsat_core                        false
% 2.93/1.00  --soft_assumptions                      false
% 2.93/1.00  --soft_lemma_size                       3
% 2.93/1.00  --prop_impl_unit_size                   0
% 2.93/1.00  --prop_impl_unit                        []
% 2.93/1.00  --share_sel_clauses                     true
% 2.93/1.00  --reset_solvers                         false
% 2.93/1.00  --bc_imp_inh                            [conj_cone]
% 2.93/1.00  --conj_cone_tolerance                   3.
% 2.93/1.00  --extra_neg_conj                        none
% 2.93/1.00  --large_theory_mode                     true
% 2.93/1.00  --prolific_symb_bound                   200
% 2.93/1.00  --lt_threshold                          2000
% 2.93/1.00  --clause_weak_htbl                      true
% 2.93/1.00  --gc_record_bc_elim                     false
% 2.93/1.00  
% 2.93/1.00  ------ Preprocessing Options
% 2.93/1.00  
% 2.93/1.00  --preprocessing_flag                    true
% 2.93/1.00  --time_out_prep_mult                    0.1
% 2.93/1.00  --splitting_mode                        input
% 2.93/1.00  --splitting_grd                         true
% 2.93/1.00  --splitting_cvd                         false
% 2.93/1.00  --splitting_cvd_svl                     false
% 2.93/1.00  --splitting_nvd                         32
% 2.93/1.00  --sub_typing                            true
% 2.93/1.00  --prep_gs_sim                           true
% 2.93/1.00  --prep_unflatten                        true
% 2.93/1.00  --prep_res_sim                          true
% 2.93/1.00  --prep_upred                            true
% 2.93/1.00  --prep_sem_filter                       exhaustive
% 2.93/1.00  --prep_sem_filter_out                   false
% 2.93/1.00  --pred_elim                             true
% 2.93/1.00  --res_sim_input                         true
% 2.93/1.00  --eq_ax_congr_red                       true
% 2.93/1.00  --pure_diseq_elim                       true
% 2.93/1.00  --brand_transform                       false
% 2.93/1.00  --non_eq_to_eq                          false
% 2.93/1.00  --prep_def_merge                        true
% 2.93/1.00  --prep_def_merge_prop_impl              false
% 2.93/1.00  --prep_def_merge_mbd                    true
% 2.93/1.00  --prep_def_merge_tr_red                 false
% 2.93/1.00  --prep_def_merge_tr_cl                  false
% 2.93/1.00  --smt_preprocessing                     true
% 2.93/1.00  --smt_ac_axioms                         fast
% 2.93/1.00  --preprocessed_out                      false
% 2.93/1.00  --preprocessed_stats                    false
% 2.93/1.00  
% 2.93/1.00  ------ Abstraction refinement Options
% 2.93/1.00  
% 2.93/1.00  --abstr_ref                             []
% 2.93/1.00  --abstr_ref_prep                        false
% 2.93/1.00  --abstr_ref_until_sat                   false
% 2.93/1.00  --abstr_ref_sig_restrict                funpre
% 2.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.00  --abstr_ref_under                       []
% 2.93/1.00  
% 2.93/1.00  ------ SAT Options
% 2.93/1.00  
% 2.93/1.00  --sat_mode                              false
% 2.93/1.00  --sat_fm_restart_options                ""
% 2.93/1.00  --sat_gr_def                            false
% 2.93/1.00  --sat_epr_types                         true
% 2.93/1.00  --sat_non_cyclic_types                  false
% 2.93/1.00  --sat_finite_models                     false
% 2.93/1.00  --sat_fm_lemmas                         false
% 2.93/1.00  --sat_fm_prep                           false
% 2.93/1.00  --sat_fm_uc_incr                        true
% 2.93/1.00  --sat_out_model                         small
% 2.93/1.00  --sat_out_clauses                       false
% 2.93/1.00  
% 2.93/1.00  ------ QBF Options
% 2.93/1.00  
% 2.93/1.00  --qbf_mode                              false
% 2.93/1.00  --qbf_elim_univ                         false
% 2.93/1.00  --qbf_dom_inst                          none
% 2.93/1.00  --qbf_dom_pre_inst                      false
% 2.93/1.00  --qbf_sk_in                             false
% 2.93/1.00  --qbf_pred_elim                         true
% 2.93/1.00  --qbf_split                             512
% 2.93/1.00  
% 2.93/1.00  ------ BMC1 Options
% 2.93/1.00  
% 2.93/1.00  --bmc1_incremental                      false
% 2.93/1.00  --bmc1_axioms                           reachable_all
% 2.93/1.00  --bmc1_min_bound                        0
% 2.93/1.00  --bmc1_max_bound                        -1
% 2.93/1.00  --bmc1_max_bound_default                -1
% 2.93/1.00  --bmc1_symbol_reachability              true
% 2.93/1.00  --bmc1_property_lemmas                  false
% 2.93/1.00  --bmc1_k_induction                      false
% 2.93/1.00  --bmc1_non_equiv_states                 false
% 2.93/1.00  --bmc1_deadlock                         false
% 2.93/1.00  --bmc1_ucm                              false
% 2.93/1.00  --bmc1_add_unsat_core                   none
% 2.93/1.00  --bmc1_unsat_core_children              false
% 2.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.00  --bmc1_out_stat                         full
% 2.93/1.00  --bmc1_ground_init                      false
% 2.93/1.00  --bmc1_pre_inst_next_state              false
% 2.93/1.00  --bmc1_pre_inst_state                   false
% 2.93/1.00  --bmc1_pre_inst_reach_state             false
% 2.93/1.00  --bmc1_out_unsat_core                   false
% 2.93/1.00  --bmc1_aig_witness_out                  false
% 2.93/1.00  --bmc1_verbose                          false
% 2.93/1.00  --bmc1_dump_clauses_tptp                false
% 2.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.00  --bmc1_dump_file                        -
% 2.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.00  --bmc1_ucm_extend_mode                  1
% 2.93/1.00  --bmc1_ucm_init_mode                    2
% 2.93/1.00  --bmc1_ucm_cone_mode                    none
% 2.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.00  --bmc1_ucm_relax_model                  4
% 2.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.00  --bmc1_ucm_layered_model                none
% 2.93/1.00  --bmc1_ucm_max_lemma_size               10
% 2.93/1.00  
% 2.93/1.00  ------ AIG Options
% 2.93/1.00  
% 2.93/1.00  --aig_mode                              false
% 2.93/1.00  
% 2.93/1.00  ------ Instantiation Options
% 2.93/1.00  
% 2.93/1.00  --instantiation_flag                    true
% 2.93/1.00  --inst_sos_flag                         false
% 2.93/1.00  --inst_sos_phase                        true
% 2.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.00  --inst_lit_sel_side                     num_symb
% 2.93/1.00  --inst_solver_per_active                1400
% 2.93/1.00  --inst_solver_calls_frac                1.
% 2.93/1.00  --inst_passive_queue_type               priority_queues
% 2.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.00  --inst_passive_queues_freq              [25;2]
% 2.93/1.00  --inst_dismatching                      true
% 2.93/1.00  --inst_eager_unprocessed_to_passive     true
% 2.93/1.00  --inst_prop_sim_given                   true
% 2.93/1.00  --inst_prop_sim_new                     false
% 2.93/1.00  --inst_subs_new                         false
% 2.93/1.00  --inst_eq_res_simp                      false
% 2.93/1.00  --inst_subs_given                       false
% 2.93/1.00  --inst_orphan_elimination               true
% 2.93/1.00  --inst_learning_loop_flag               true
% 2.93/1.00  --inst_learning_start                   3000
% 2.93/1.00  --inst_learning_factor                  2
% 2.93/1.00  --inst_start_prop_sim_after_learn       3
% 2.93/1.00  --inst_sel_renew                        solver
% 2.93/1.00  --inst_lit_activity_flag                true
% 2.93/1.00  --inst_restr_to_given                   false
% 2.93/1.00  --inst_activity_threshold               500
% 2.93/1.00  --inst_out_proof                        true
% 2.93/1.00  
% 2.93/1.00  ------ Resolution Options
% 2.93/1.00  
% 2.93/1.00  --resolution_flag                       true
% 2.93/1.00  --res_lit_sel                           adaptive
% 2.93/1.00  --res_lit_sel_side                      none
% 2.93/1.00  --res_ordering                          kbo
% 2.93/1.00  --res_to_prop_solver                    active
% 2.93/1.00  --res_prop_simpl_new                    false
% 2.93/1.00  --res_prop_simpl_given                  true
% 2.93/1.00  --res_passive_queue_type                priority_queues
% 2.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.00  --res_passive_queues_freq               [15;5]
% 2.93/1.00  --res_forward_subs                      full
% 2.93/1.00  --res_backward_subs                     full
% 2.93/1.00  --res_forward_subs_resolution           true
% 2.93/1.00  --res_backward_subs_resolution          true
% 2.93/1.00  --res_orphan_elimination                true
% 2.93/1.00  --res_time_limit                        2.
% 2.93/1.00  --res_out_proof                         true
% 2.93/1.00  
% 2.93/1.00  ------ Superposition Options
% 2.93/1.00  
% 2.93/1.00  --superposition_flag                    true
% 2.93/1.00  --sup_passive_queue_type                priority_queues
% 2.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.00  --demod_completeness_check              fast
% 2.93/1.00  --demod_use_ground                      true
% 2.93/1.00  --sup_to_prop_solver                    passive
% 2.93/1.00  --sup_prop_simpl_new                    true
% 2.93/1.00  --sup_prop_simpl_given                  true
% 2.93/1.00  --sup_fun_splitting                     false
% 2.93/1.00  --sup_smt_interval                      50000
% 2.93/1.00  
% 2.93/1.00  ------ Superposition Simplification Setup
% 2.93/1.00  
% 2.93/1.00  --sup_indices_passive                   []
% 2.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.00  --sup_full_bw                           [BwDemod]
% 2.93/1.00  --sup_immed_triv                        [TrivRules]
% 2.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.00  --sup_immed_bw_main                     []
% 2.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.00  
% 2.93/1.00  ------ Combination Options
% 2.93/1.00  
% 2.93/1.00  --comb_res_mult                         3
% 2.93/1.00  --comb_sup_mult                         2
% 2.93/1.00  --comb_inst_mult                        10
% 2.93/1.00  
% 2.93/1.00  ------ Debug Options
% 2.93/1.00  
% 2.93/1.00  --dbg_backtrace                         false
% 2.93/1.00  --dbg_dump_prop_clauses                 false
% 2.93/1.00  --dbg_dump_prop_clauses_file            -
% 2.93/1.00  --dbg_out_stat                          false
% 2.93/1.00  ------ Parsing...
% 2.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/1.00  
% 2.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.93/1.00  
% 2.93/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/1.00  
% 2.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/1.00  ------ Proving...
% 2.93/1.00  ------ Problem Properties 
% 2.93/1.00  
% 2.93/1.00  
% 2.93/1.00  clauses                                 27
% 2.93/1.00  conjectures                             3
% 2.93/1.00  EPR                                     10
% 2.93/1.00  Horn                                    27
% 2.93/1.00  unary                                   8
% 2.93/1.00  binary                                  3
% 2.93/1.00  lits                                    80
% 2.93/1.00  lits eq                                 6
% 2.93/1.00  fd_pure                                 0
% 2.93/1.00  fd_pseudo                               0
% 2.93/1.00  fd_cond                                 0
% 2.93/1.00  fd_pseudo_cond                          1
% 2.93/1.00  AC symbols                              0
% 2.93/1.00  
% 2.93/1.00  ------ Schedule dynamic 5 is on 
% 2.93/1.00  
% 2.93/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/1.00  
% 2.93/1.00  
% 2.93/1.00  ------ 
% 2.93/1.00  Current options:
% 2.93/1.00  ------ 
% 2.93/1.00  
% 2.93/1.00  ------ Input Options
% 2.93/1.00  
% 2.93/1.00  --out_options                           all
% 2.93/1.00  --tptp_safe_out                         true
% 2.93/1.00  --problem_path                          ""
% 2.93/1.00  --include_path                          ""
% 2.93/1.00  --clausifier                            res/vclausify_rel
% 2.93/1.00  --clausifier_options                    --mode clausify
% 2.93/1.00  --stdin                                 false
% 2.93/1.00  --stats_out                             all
% 2.93/1.00  
% 2.93/1.00  ------ General Options
% 2.93/1.00  
% 2.93/1.00  --fof                                   false
% 2.93/1.00  --time_out_real                         305.
% 2.93/1.00  --time_out_virtual                      -1.
% 2.93/1.00  --symbol_type_check                     false
% 2.93/1.00  --clausify_out                          false
% 2.93/1.00  --sig_cnt_out                           false
% 2.93/1.00  --trig_cnt_out                          false
% 2.93/1.00  --trig_cnt_out_tolerance                1.
% 2.93/1.00  --trig_cnt_out_sk_spl                   false
% 2.93/1.00  --abstr_cl_out                          false
% 2.93/1.00  
% 2.93/1.00  ------ Global Options
% 2.93/1.00  
% 2.93/1.00  --schedule                              default
% 2.93/1.00  --add_important_lit                     false
% 2.93/1.00  --prop_solver_per_cl                    1000
% 2.93/1.00  --min_unsat_core                        false
% 2.93/1.00  --soft_assumptions                      false
% 2.93/1.00  --soft_lemma_size                       3
% 2.93/1.00  --prop_impl_unit_size                   0
% 2.93/1.00  --prop_impl_unit                        []
% 2.93/1.00  --share_sel_clauses                     true
% 2.93/1.00  --reset_solvers                         false
% 2.93/1.00  --bc_imp_inh                            [conj_cone]
% 2.93/1.00  --conj_cone_tolerance                   3.
% 2.93/1.00  --extra_neg_conj                        none
% 2.93/1.00  --large_theory_mode                     true
% 2.93/1.00  --prolific_symb_bound                   200
% 2.93/1.00  --lt_threshold                          2000
% 2.93/1.00  --clause_weak_htbl                      true
% 2.93/1.00  --gc_record_bc_elim                     false
% 2.93/1.00  
% 2.93/1.00  ------ Preprocessing Options
% 2.93/1.00  
% 2.93/1.00  --preprocessing_flag                    true
% 2.93/1.00  --time_out_prep_mult                    0.1
% 2.93/1.00  --splitting_mode                        input
% 2.93/1.00  --splitting_grd                         true
% 2.93/1.00  --splitting_cvd                         false
% 2.93/1.00  --splitting_cvd_svl                     false
% 2.93/1.00  --splitting_nvd                         32
% 2.93/1.00  --sub_typing                            true
% 2.93/1.00  --prep_gs_sim                           true
% 2.93/1.00  --prep_unflatten                        true
% 2.93/1.00  --prep_res_sim                          true
% 2.93/1.00  --prep_upred                            true
% 2.93/1.00  --prep_sem_filter                       exhaustive
% 2.93/1.00  --prep_sem_filter_out                   false
% 2.93/1.00  --pred_elim                             true
% 2.93/1.00  --res_sim_input                         true
% 2.93/1.00  --eq_ax_congr_red                       true
% 2.93/1.00  --pure_diseq_elim                       true
% 2.93/1.00  --brand_transform                       false
% 2.93/1.00  --non_eq_to_eq                          false
% 2.93/1.00  --prep_def_merge                        true
% 2.93/1.00  --prep_def_merge_prop_impl              false
% 2.93/1.00  --prep_def_merge_mbd                    true
% 2.93/1.00  --prep_def_merge_tr_red                 false
% 2.93/1.00  --prep_def_merge_tr_cl                  false
% 2.93/1.00  --smt_preprocessing                     true
% 2.93/1.00  --smt_ac_axioms                         fast
% 2.93/1.00  --preprocessed_out                      false
% 2.93/1.00  --preprocessed_stats                    false
% 2.93/1.00  
% 2.93/1.00  ------ Abstraction refinement Options
% 2.93/1.00  
% 2.93/1.00  --abstr_ref                             []
% 2.93/1.00  --abstr_ref_prep                        false
% 2.93/1.00  --abstr_ref_until_sat                   false
% 2.93/1.00  --abstr_ref_sig_restrict                funpre
% 2.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.00  --abstr_ref_under                       []
% 2.93/1.00  
% 2.93/1.00  ------ SAT Options
% 2.93/1.00  
% 2.93/1.00  --sat_mode                              false
% 2.93/1.00  --sat_fm_restart_options                ""
% 2.93/1.00  --sat_gr_def                            false
% 2.93/1.00  --sat_epr_types                         true
% 2.93/1.00  --sat_non_cyclic_types                  false
% 2.93/1.00  --sat_finite_models                     false
% 2.93/1.00  --sat_fm_lemmas                         false
% 2.93/1.00  --sat_fm_prep                           false
% 2.93/1.00  --sat_fm_uc_incr                        true
% 2.93/1.00  --sat_out_model                         small
% 2.93/1.00  --sat_out_clauses                       false
% 2.93/1.00  
% 2.93/1.00  ------ QBF Options
% 2.93/1.00  
% 2.93/1.00  --qbf_mode                              false
% 2.93/1.00  --qbf_elim_univ                         false
% 2.93/1.00  --qbf_dom_inst                          none
% 2.93/1.00  --qbf_dom_pre_inst                      false
% 2.93/1.00  --qbf_sk_in                             false
% 2.93/1.00  --qbf_pred_elim                         true
% 2.93/1.00  --qbf_split                             512
% 2.93/1.00  
% 2.93/1.00  ------ BMC1 Options
% 2.93/1.00  
% 2.93/1.00  --bmc1_incremental                      false
% 2.93/1.00  --bmc1_axioms                           reachable_all
% 2.93/1.00  --bmc1_min_bound                        0
% 2.93/1.00  --bmc1_max_bound                        -1
% 2.93/1.00  --bmc1_max_bound_default                -1
% 2.93/1.00  --bmc1_symbol_reachability              true
% 2.93/1.00  --bmc1_property_lemmas                  false
% 2.93/1.00  --bmc1_k_induction                      false
% 2.93/1.00  --bmc1_non_equiv_states                 false
% 2.93/1.00  --bmc1_deadlock                         false
% 2.93/1.00  --bmc1_ucm                              false
% 2.93/1.00  --bmc1_add_unsat_core                   none
% 2.93/1.00  --bmc1_unsat_core_children              false
% 2.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.00  --bmc1_out_stat                         full
% 2.93/1.00  --bmc1_ground_init                      false
% 2.93/1.00  --bmc1_pre_inst_next_state              false
% 2.93/1.00  --bmc1_pre_inst_state                   false
% 2.93/1.00  --bmc1_pre_inst_reach_state             false
% 2.93/1.00  --bmc1_out_unsat_core                   false
% 2.93/1.00  --bmc1_aig_witness_out                  false
% 2.93/1.00  --bmc1_verbose                          false
% 2.93/1.00  --bmc1_dump_clauses_tptp                false
% 2.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.00  --bmc1_dump_file                        -
% 2.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.00  --bmc1_ucm_extend_mode                  1
% 2.93/1.00  --bmc1_ucm_init_mode                    2
% 2.93/1.00  --bmc1_ucm_cone_mode                    none
% 2.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.00  --bmc1_ucm_relax_model                  4
% 2.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.00  --bmc1_ucm_layered_model                none
% 2.93/1.00  --bmc1_ucm_max_lemma_size               10
% 2.93/1.00  
% 2.93/1.00  ------ AIG Options
% 2.93/1.00  
% 2.93/1.00  --aig_mode                              false
% 2.93/1.00  
% 2.93/1.00  ------ Instantiation Options
% 2.93/1.00  
% 2.93/1.00  --instantiation_flag                    true
% 2.93/1.00  --inst_sos_flag                         false
% 2.93/1.00  --inst_sos_phase                        true
% 2.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.00  --inst_lit_sel_side                     none
% 2.93/1.00  --inst_solver_per_active                1400
% 2.93/1.00  --inst_solver_calls_frac                1.
% 2.93/1.00  --inst_passive_queue_type               priority_queues
% 2.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.00  --inst_passive_queues_freq              [25;2]
% 2.93/1.00  --inst_dismatching                      true
% 2.93/1.00  --inst_eager_unprocessed_to_passive     true
% 2.93/1.00  --inst_prop_sim_given                   true
% 2.93/1.00  --inst_prop_sim_new                     false
% 2.93/1.00  --inst_subs_new                         false
% 2.93/1.00  --inst_eq_res_simp                      false
% 2.93/1.00  --inst_subs_given                       false
% 2.93/1.00  --inst_orphan_elimination               true
% 2.93/1.00  --inst_learning_loop_flag               true
% 2.93/1.00  --inst_learning_start                   3000
% 2.93/1.00  --inst_learning_factor                  2
% 2.93/1.00  --inst_start_prop_sim_after_learn       3
% 2.93/1.00  --inst_sel_renew                        solver
% 2.93/1.00  --inst_lit_activity_flag                true
% 2.93/1.00  --inst_restr_to_given                   false
% 2.93/1.00  --inst_activity_threshold               500
% 2.93/1.00  --inst_out_proof                        true
% 2.93/1.00  
% 2.93/1.00  ------ Resolution Options
% 2.93/1.00  
% 2.93/1.00  --resolution_flag                       false
% 2.93/1.00  --res_lit_sel                           adaptive
% 2.93/1.00  --res_lit_sel_side                      none
% 2.93/1.00  --res_ordering                          kbo
% 2.93/1.00  --res_to_prop_solver                    active
% 2.93/1.00  --res_prop_simpl_new                    false
% 2.93/1.00  --res_prop_simpl_given                  true
% 2.93/1.00  --res_passive_queue_type                priority_queues
% 2.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.00  --res_passive_queues_freq               [15;5]
% 2.93/1.00  --res_forward_subs                      full
% 2.93/1.00  --res_backward_subs                     full
% 2.93/1.00  --res_forward_subs_resolution           true
% 2.93/1.00  --res_backward_subs_resolution          true
% 2.93/1.00  --res_orphan_elimination                true
% 2.93/1.00  --res_time_limit                        2.
% 2.93/1.00  --res_out_proof                         true
% 2.93/1.00  
% 2.93/1.00  ------ Superposition Options
% 2.93/1.00  
% 2.93/1.00  --superposition_flag                    true
% 2.93/1.00  --sup_passive_queue_type                priority_queues
% 2.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.00  --demod_completeness_check              fast
% 2.93/1.00  --demod_use_ground                      true
% 2.93/1.00  --sup_to_prop_solver                    passive
% 2.93/1.00  --sup_prop_simpl_new                    true
% 2.93/1.00  --sup_prop_simpl_given                  true
% 2.93/1.00  --sup_fun_splitting                     false
% 2.93/1.00  --sup_smt_interval                      50000
% 2.93/1.00  
% 2.93/1.00  ------ Superposition Simplification Setup
% 2.93/1.00  
% 2.93/1.00  --sup_indices_passive                   []
% 2.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.00  --sup_full_bw                           [BwDemod]
% 2.93/1.00  --sup_immed_triv                        [TrivRules]
% 2.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.00  --sup_immed_bw_main                     []
% 2.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.00  
% 2.93/1.00  ------ Combination Options
% 2.93/1.00  
% 2.93/1.00  --comb_res_mult                         3
% 2.93/1.00  --comb_sup_mult                         2
% 2.93/1.00  --comb_inst_mult                        10
% 2.93/1.00  
% 2.93/1.00  ------ Debug Options
% 2.93/1.00  
% 2.93/1.00  --dbg_backtrace                         false
% 2.93/1.00  --dbg_dump_prop_clauses                 false
% 2.93/1.00  --dbg_dump_prop_clauses_file            -
% 2.93/1.00  --dbg_out_stat                          false
% 2.93/1.00  
% 2.93/1.00  
% 2.93/1.00  
% 2.93/1.00  
% 2.93/1.00  ------ Proving...
% 2.93/1.00  
% 2.93/1.00  
% 2.93/1.00  % SZS status Theorem for theBenchmark.p
% 2.93/1.00  
% 2.93/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/1.00  
% 2.93/1.00  fof(f8,axiom,(
% 2.93/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.00  
% 2.93/1.00  fof(f30,plain,(
% 2.93/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.93/1.00    inference(ennf_transformation,[],[f8])).
% 2.93/1.00  
% 2.93/1.00  fof(f68,plain,(
% 2.93/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.93/1.00    inference(cnf_transformation,[],[f30])).
% 2.93/1.00  
% 2.93/1.00  fof(f15,axiom,(
% 2.93/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.00  
% 2.93/1.00  fof(f39,plain,(
% 2.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.93/1.00    inference(ennf_transformation,[],[f15])).
% 2.93/1.00  
% 2.93/1.00  fof(f40,plain,(
% 2.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.93/1.00    inference(flattening,[],[f39])).
% 2.93/1.00  
% 2.93/1.00  fof(f53,plain,(
% 2.93/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.93/1.00    inference(nnf_transformation,[],[f40])).
% 2.93/1.00  
% 2.93/1.00  fof(f78,plain,(
% 2.93/1.00    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.93/1.00    inference(cnf_transformation,[],[f53])).
% 2.93/1.00  
% 2.93/1.00  fof(f9,axiom,(
% 2.93/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 2.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.00  
% 2.93/1.00  fof(f31,plain,(
% 2.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.93/1.00    inference(ennf_transformation,[],[f9])).
% 2.93/1.00  
% 2.93/1.00  fof(f32,plain,(
% 2.93/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.93/1.00    inference(flattening,[],[f31])).
% 2.93/1.00  
% 2.93/1.00  fof(f69,plain,(
% 2.93/1.00    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f32])).
% 2.93/1.01  
% 2.93/1.01  fof(f90,plain,(
% 2.93/1.01    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(equality_resolution,[],[f69])).
% 2.93/1.01  
% 2.93/1.01  fof(f10,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f33,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f10])).
% 2.93/1.01  
% 2.93/1.01  fof(f51,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(nnf_transformation,[],[f33])).
% 2.93/1.01  
% 2.93/1.01  fof(f70,plain,(
% 2.93/1.01    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f51])).
% 2.93/1.01  
% 2.93/1.01  fof(f1,axiom,(
% 2.93/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f48,plain,(
% 2.93/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.93/1.01    inference(nnf_transformation,[],[f1])).
% 2.93/1.01  
% 2.93/1.01  fof(f49,plain,(
% 2.93/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.93/1.01    inference(flattening,[],[f48])).
% 2.93/1.01  
% 2.93/1.01  fof(f60,plain,(
% 2.93/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f49])).
% 2.93/1.01  
% 2.93/1.01  fof(f4,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f25,plain,(
% 2.93/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f4])).
% 2.93/1.01  
% 2.93/1.01  fof(f63,plain,(
% 2.93/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f25])).
% 2.93/1.01  
% 2.93/1.01  fof(f14,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f38,plain,(
% 2.93/1.01    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f14])).
% 2.93/1.01  
% 2.93/1.01  fof(f76,plain,(
% 2.93/1.01    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f38])).
% 2.93/1.01  
% 2.93/1.01  fof(f7,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f29,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f7])).
% 2.93/1.01  
% 2.93/1.01  fof(f50,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(nnf_transformation,[],[f29])).
% 2.93/1.01  
% 2.93/1.01  fof(f66,plain,(
% 2.93/1.01    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f50])).
% 2.93/1.01  
% 2.93/1.01  fof(f3,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f24,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f3])).
% 2.93/1.01  
% 2.93/1.01  fof(f62,plain,(
% 2.93/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f24])).
% 2.93/1.01  
% 2.93/1.01  fof(f19,conjecture,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f20,negated_conjecture,(
% 2.93/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 2.93/1.01    inference(negated_conjecture,[],[f19])).
% 2.93/1.01  
% 2.93/1.01  fof(f46,plain,(
% 2.93/1.01    ? [X0] : (? [X1] : ((~v1_tdlat_3(X1) & (v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f20])).
% 2.93/1.01  
% 2.93/1.01  fof(f47,plain,(
% 2.93/1.01    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 2.93/1.01    inference(flattening,[],[f46])).
% 2.93/1.01  
% 2.93/1.01  fof(f56,plain,(
% 2.93/1.01    ( ! [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v1_tdlat_3(sK1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK1))) )),
% 2.93/1.01    introduced(choice_axiom,[])).
% 2.93/1.01  
% 2.93/1.01  fof(f55,plain,(
% 2.93/1.01    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 2.93/1.01    introduced(choice_axiom,[])).
% 2.93/1.01  
% 2.93/1.01  fof(f57,plain,(
% 2.93/1.01    (~v1_tdlat_3(sK1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 2.93/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f56,f55])).
% 2.93/1.01  
% 2.93/1.01  fof(f85,plain,(
% 2.93/1.01    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 2.93/1.01    inference(cnf_transformation,[],[f57])).
% 2.93/1.01  
% 2.93/1.01  fof(f6,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f28,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f6])).
% 2.93/1.01  
% 2.93/1.01  fof(f65,plain,(
% 2.93/1.01    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f28])).
% 2.93/1.01  
% 2.93/1.01  fof(f83,plain,(
% 2.93/1.01    l1_pre_topc(sK0)),
% 2.93/1.01    inference(cnf_transformation,[],[f57])).
% 2.93/1.01  
% 2.93/1.01  fof(f84,plain,(
% 2.93/1.01    l1_pre_topc(sK1)),
% 2.93/1.01    inference(cnf_transformation,[],[f57])).
% 2.93/1.01  
% 2.93/1.01  fof(f16,axiom,(
% 2.93/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f41,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.93/1.01    inference(ennf_transformation,[],[f16])).
% 2.93/1.01  
% 2.93/1.01  fof(f42,plain,(
% 2.93/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.93/1.01    inference(flattening,[],[f41])).
% 2.93/1.01  
% 2.93/1.01  fof(f79,plain,(
% 2.93/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f42])).
% 2.93/1.01  
% 2.93/1.01  fof(f11,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f34,plain,(
% 2.93/1.01    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f11])).
% 2.93/1.01  
% 2.93/1.01  fof(f72,plain,(
% 2.93/1.01    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f34])).
% 2.93/1.01  
% 2.93/1.01  fof(f18,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f45,plain,(
% 2.93/1.01    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f18])).
% 2.93/1.01  
% 2.93/1.01  fof(f54,plain,(
% 2.93/1.01    ! [X0] : (((v1_tdlat_3(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))) & (u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(nnf_transformation,[],[f45])).
% 2.93/1.01  
% 2.93/1.01  fof(f82,plain,(
% 2.93/1.01    ( ! [X0] : (v1_tdlat_3(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f54])).
% 2.93/1.01  
% 2.93/1.01  fof(f87,plain,(
% 2.93/1.01    ~v1_tdlat_3(sK1)),
% 2.93/1.01    inference(cnf_transformation,[],[f57])).
% 2.93/1.01  
% 2.93/1.01  fof(f58,plain,(
% 2.93/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.93/1.01    inference(cnf_transformation,[],[f49])).
% 2.93/1.01  
% 2.93/1.01  fof(f89,plain,(
% 2.93/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.93/1.01    inference(equality_resolution,[],[f58])).
% 2.93/1.01  
% 2.93/1.01  fof(f17,axiom,(
% 2.93/1.01    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.01  
% 2.93/1.01  fof(f43,plain,(
% 2.93/1.01    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(ennf_transformation,[],[f17])).
% 2.93/1.01  
% 2.93/1.01  fof(f44,plain,(
% 2.93/1.01    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.93/1.01    inference(flattening,[],[f43])).
% 2.93/1.01  
% 2.93/1.01  fof(f80,plain,(
% 2.93/1.01    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f44])).
% 2.93/1.01  
% 2.93/1.01  fof(f81,plain,(
% 2.93/1.01    ( ! [X0] : (u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.93/1.01    inference(cnf_transformation,[],[f54])).
% 2.93/1.01  
% 2.93/1.01  fof(f86,plain,(
% 2.93/1.01    v1_tdlat_3(sK0)),
% 2.93/1.01    inference(cnf_transformation,[],[f57])).
% 2.93/1.01  
% 2.93/1.01  cnf(c_10,plain,
% 2.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.93/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 2.93/1.01      | ~ m1_pre_topc(X1,X2)
% 2.93/1.01      | ~ l1_pre_topc(X2) ),
% 2.93/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1213,plain,
% 2.93/1.01      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.93/1.01      | ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_12087,plain,
% 2.93/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.93/1.01      | ~ m1_pre_topc(sK1,sK0)
% 2.93/1.01      | ~ l1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1213]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_19,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | ~ m1_pre_topc(X0,X2)
% 2.93/1.01      | ~ m1_pre_topc(X2,X1)
% 2.93/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.93/1.01      | ~ l1_pre_topc(X1)
% 2.93/1.01      | ~ v2_pre_topc(X1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2444,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | ~ m1_pre_topc(X0,sK0)
% 2.93/1.01      | ~ m1_pre_topc(sK0,X1)
% 2.93/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
% 2.93/1.01      | ~ l1_pre_topc(X1)
% 2.93/1.01      | ~ v2_pre_topc(X1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_10032,plain,
% 2.93/1.01      ( ~ m1_pre_topc(sK0,X0)
% 2.93/1.01      | ~ m1_pre_topc(sK1,X0)
% 2.93/1.01      | ~ m1_pre_topc(sK1,sK0)
% 2.93/1.01      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
% 2.93/1.01      | ~ l1_pre_topc(X0)
% 2.93/1.01      | ~ v2_pre_topc(X0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_2444]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_10034,plain,
% 2.93/1.01      ( ~ m1_pre_topc(sK0,sK0)
% 2.93/1.01      | ~ m1_pre_topc(sK1,sK0)
% 2.93/1.01      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
% 2.93/1.01      | ~ l1_pre_topc(sK0)
% 2.93/1.01      | ~ v2_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_10032]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_11,plain,
% 2.93/1.01      ( ~ v1_tops_2(X0,X1)
% 2.93/1.01      | v1_tops_2(X0,X2)
% 2.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 2.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.93/1.01      | ~ m1_pre_topc(X2,X1)
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1237,plain,
% 2.93/1.01      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 2.93/1.01      | v1_tops_2(u1_pre_topc(X0),X1)
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.93/1.01      | ~ m1_pre_topc(X1,X0)
% 2.93/1.01      | ~ l1_pre_topc(X0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_9537,plain,
% 2.93/1.01      ( v1_tops_2(u1_pre_topc(sK1),sK0)
% 2.93/1.01      | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.93/1.01      | ~ m1_pre_topc(sK0,sK1)
% 2.93/1.01      | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1237]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_13,plain,
% 2.93/1.01      ( ~ v1_tops_2(X0,X1)
% 2.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.93/1.01      | r1_tarski(X0,u1_pre_topc(X1))
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1329,plain,
% 2.93/1.01      ( ~ v1_tops_2(u1_pre_topc(X0),X1)
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.93/1.01      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_6618,plain,
% 2.93/1.01      ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
% 2.93/1.01      | ~ l1_pre_topc(X0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1329]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_6620,plain,
% 2.93/1.01      ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
% 2.93/1.01      | ~ l1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_6618]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_0,plain,
% 2.93/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.93/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1828,plain,
% 2.93/1.01      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 2.93/1.01      | ~ r1_tarski(u1_struct_0(sK0),X0)
% 2.93/1.01      | X0 = u1_struct_0(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2443,plain,
% 2.93/1.01      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
% 2.93/1.01      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))
% 2.93/1.01      | u1_struct_0(X0) = u1_struct_0(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1828]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_5850,plain,
% 2.93/1.01      ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
% 2.93/1.01      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
% 2.93/1.01      | u1_struct_0(sK1) = u1_struct_0(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_2443]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_5,plain,
% 2.93/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | ~ l1_pre_topc(X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_4924,plain,
% 2.93/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.93/1.01      | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_527,plain,
% 2.93/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.93/1.01      theory(equality) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1227,plain,
% 2.93/1.01      ( ~ r1_tarski(X0,X1)
% 2.93/1.01      | r1_tarski(X2,u1_pre_topc(X3))
% 2.93/1.01      | X2 != X0
% 2.93/1.01      | u1_pre_topc(X3) != X1 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_527]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1297,plain,
% 2.93/1.01      ( ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.93/1.01      | r1_tarski(X2,u1_pre_topc(X1))
% 2.93/1.01      | X2 != X0
% 2.93/1.01      | u1_pre_topc(X1) != u1_pre_topc(X1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1227]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1644,plain,
% 2.93/1.01      ( r1_tarski(X0,u1_pre_topc(X1))
% 2.93/1.01      | ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(X1))
% 2.93/1.01      | X0 != k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_pre_topc(X1) != u1_pre_topc(X1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1297]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2950,plain,
% 2.93/1.01      ( ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(X0))
% 2.93/1.01      | r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
% 2.93/1.01      | u1_pre_topc(X1) != k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_pre_topc(X0) != u1_pre_topc(X0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1644]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_4404,plain,
% 2.93/1.01      ( ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(sK1))
% 2.93/1.01      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 2.93/1.01      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_2950]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_4406,plain,
% 2.93/1.01      ( ~ r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(sK1))
% 2.93/1.01      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
% 2.93/1.01      | u1_pre_topc(sK0) != k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_4404]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_537,plain,
% 2.93/1.01      ( X0 != X1 | k9_setfam_1(X0) = k9_setfam_1(X1) ),
% 2.93/1.01      theory(equality) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1432,plain,
% 2.93/1.01      ( X0 != u1_struct_0(sK0)
% 2.93/1.01      | k9_setfam_1(X0) = k9_setfam_1(u1_struct_0(sK0)) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_537]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1837,plain,
% 2.93/1.01      ( k9_setfam_1(u1_struct_0(X0)) = k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1432]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_4002,plain,
% 2.93/1.01      ( k9_setfam_1(u1_struct_0(sK1)) = k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_struct_0(sK1) != u1_struct_0(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1837]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_18,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_966,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X0) = iProver_top
% 2.93/1.01      | l1_pre_topc(X0) != iProver_top ),
% 2.93/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_9,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.93/1.01      | ~ l1_pre_topc(X0)
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_4,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_175,plain,
% 2.93/1.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.93/1.01      | ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(global_propositional_subsumption,[status(thm)],[c_9,c_4]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_176,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(renaming,[status(thm)],[c_175]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_959,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 2.93/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.93/1.01      | l1_pre_topc(X1) != iProver_top ),
% 2.93/1.01      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_27,negated_conjecture,
% 2.93/1.01      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 2.93/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_7,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X1)
% 2.93/1.01      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_973,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X1) = iProver_top
% 2.93/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.93/1.01      | l1_pre_topc(X1) != iProver_top ),
% 2.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1879,plain,
% 2.93/1.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK0) = iProver_top
% 2.93/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 2.93/1.01      inference(superposition,[status(thm)],[c_27,c_973]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_29,negated_conjecture,
% 2.93/1.01      ( l1_pre_topc(sK0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_30,plain,
% 2.93/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 2.93/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2055,plain,
% 2.93/1.01      ( m1_pre_topc(X0,sK0) = iProver_top
% 2.93/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.93/1.01      inference(global_propositional_subsumption,
% 2.93/1.01                [status(thm)],
% 2.93/1.01                [c_1879,c_30]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2056,plain,
% 2.93/1.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK0) = iProver_top ),
% 2.93/1.01      inference(renaming,[status(thm)],[c_2055]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2063,plain,
% 2.93/1.01      ( m1_pre_topc(X0,sK0) = iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK1) != iProver_top
% 2.93/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.93/1.01      inference(superposition,[status(thm)],[c_959,c_2056]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_28,negated_conjecture,
% 2.93/1.01      ( l1_pre_topc(sK1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_31,plain,
% 2.93/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 2.93/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2253,plain,
% 2.93/1.01      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK0) = iProver_top ),
% 2.93/1.01      inference(global_propositional_subsumption,
% 2.93/1.01                [status(thm)],
% 2.93/1.01                [c_2063,c_31]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2254,plain,
% 2.93/1.01      ( m1_pre_topc(X0,sK0) = iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.93/1.01      inference(renaming,[status(thm)],[c_2253]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2262,plain,
% 2.93/1.01      ( m1_pre_topc(sK1,sK0) = iProver_top
% 2.93/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.93/1.01      inference(superposition,[status(thm)],[c_966,c_2254]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_3753,plain,
% 2.93/1.01      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 2.93/1.01      inference(global_propositional_subsumption,
% 2.93/1.01                [status(thm)],
% 2.93/1.01                [c_2262,c_31]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_965,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 2.93/1.01      | m1_pre_topc(X2,X1) != iProver_top
% 2.93/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 2.93/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 2.93/1.01      | l1_pre_topc(X1) != iProver_top
% 2.93/1.01      | v2_pre_topc(X1) != iProver_top ),
% 2.93/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_21,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | ~ m1_pre_topc(X2,X0)
% 2.93/1.01      | m1_pre_topc(X2,X1)
% 2.93/1.01      | ~ l1_pre_topc(X1)
% 2.93/1.01      | ~ v2_pre_topc(X1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_963,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 2.93/1.01      | m1_pre_topc(X2,X0) != iProver_top
% 2.93/1.01      | m1_pre_topc(X2,X1) = iProver_top
% 2.93/1.01      | l1_pre_topc(X1) != iProver_top
% 2.93/1.01      | v2_pre_topc(X1) != iProver_top ),
% 2.93/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1110,plain,
% 2.93/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 2.93/1.01      | m1_pre_topc(X2,X0) != iProver_top
% 2.93/1.01      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 2.93/1.01      | l1_pre_topc(X1) != iProver_top
% 2.93/1.01      | v2_pre_topc(X1) != iProver_top ),
% 2.93/1.01      inference(forward_subsumption_resolution,
% 2.93/1.01                [status(thm)],
% 2.93/1.01                [c_965,c_963]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_3758,plain,
% 2.93/1.01      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.93/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
% 2.93/1.01      | l1_pre_topc(sK0) != iProver_top
% 2.93/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 2.93/1.01      inference(superposition,[status(thm)],[c_3753,c_1110]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_3779,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,sK1)
% 2.93/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))
% 2.93/1.01      | ~ l1_pre_topc(sK0)
% 2.93/1.01      | ~ v2_pre_topc(sK0) ),
% 2.93/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3758]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_3781,plain,
% 2.93/1.01      ( ~ m1_pre_topc(sK0,sK1)
% 2.93/1.01      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
% 2.93/1.01      | ~ l1_pre_topc(sK0)
% 2.93/1.01      | ~ v2_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_3779]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1364,plain,
% 2.93/1.01      ( ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.93/1.01      | ~ m1_pre_topc(X0,X1)
% 2.93/1.01      | ~ l1_pre_topc(X1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2991,plain,
% 2.93/1.01      ( ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.93/1.01      | ~ m1_pre_topc(X0,sK1)
% 2.93/1.01      | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1364]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2993,plain,
% 2.93/1.01      ( ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.93/1.01      | ~ m1_pre_topc(sK0,sK1)
% 2.93/1.01      | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_2991]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_526,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1204,plain,
% 2.93/1.01      ( k9_setfam_1(u1_struct_0(sK1)) != X0
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 2.93/1.01      | u1_pre_topc(sK1) != X0 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_526]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2939,plain,
% 2.93/1.01      ( k9_setfam_1(u1_struct_0(sK1)) != k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 2.93/1.01      | u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0)) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1204]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1429,plain,
% 2.93/1.01      ( X0 != X1
% 2.93/1.01      | X0 = k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK0)) != X1 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_526]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1981,plain,
% 2.93/1.01      ( X0 = k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | X0 != u1_pre_topc(sK0)
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2017,plain,
% 2.93/1.01      ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 2.93/1.01      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1981]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2938,plain,
% 2.93/1.01      ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 2.93/1.01      | u1_pre_topc(sK1) = k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_2017]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_14,plain,
% 2.93/1.01      ( v1_tops_2(u1_pre_topc(X0),X0) | ~ l1_pre_topc(X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2422,plain,
% 2.93/1.01      ( v1_tops_2(u1_pre_topc(sK1),sK1) | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2283,plain,
% 2.93/1.01      ( m1_pre_topc(sK1,sK0) | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2262]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1337,plain,
% 2.93/1.01      ( v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),X0)
% 2.93/1.01      | ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK0)
% 2.93/1.01      | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | ~ m1_pre_topc(X0,sK0)
% 2.93/1.01      | ~ l1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2024,plain,
% 2.93/1.01      ( ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK0)
% 2.93/1.01      | v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK1)
% 2.93/1.01      | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.93/1.01      | ~ m1_pre_topc(sK1,sK0)
% 2.93/1.01      | ~ l1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1337]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2019,plain,
% 2.93/1.01      ( k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 2.93/1.01      | u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))
% 2.93/1.01      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_2017]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1544,plain,
% 2.93/1.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK0) != iProver_top
% 2.93/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 2.93/1.01      inference(superposition,[status(thm)],[c_27,c_959]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1629,plain,
% 2.93/1.01      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.93/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.93/1.01      inference(global_propositional_subsumption,
% 2.93/1.01                [status(thm)],
% 2.93/1.01                [c_1544,c_30]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1630,plain,
% 2.93/1.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK0) != iProver_top ),
% 2.93/1.01      inference(renaming,[status(thm)],[c_1629]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1878,plain,
% 2.93/1.01      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.93/1.01      | m1_pre_topc(X0,sK1) = iProver_top
% 2.93/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.93/1.01      inference(superposition,[status(thm)],[c_1630,c_973]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1912,plain,
% 2.93/1.01      ( ~ m1_pre_topc(X0,sK0)
% 2.93/1.01      | m1_pre_topc(X0,sK1)
% 2.93/1.01      | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1878]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1914,plain,
% 2.93/1.01      ( ~ m1_pre_topc(sK0,sK0)
% 2.93/1.01      | m1_pre_topc(sK0,sK1)
% 2.93/1.01      | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1912]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1385,plain,
% 2.93/1.01      ( ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),X0)
% 2.93/1.01      | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(X0))
% 2.93/1.01      | ~ l1_pre_topc(X0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1664,plain,
% 2.93/1.01      ( ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK1)
% 2.93/1.01      | ~ m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.93/1.01      | r1_tarski(k9_setfam_1(u1_struct_0(sK0)),u1_pre_topc(sK1))
% 2.93/1.01      | ~ l1_pre_topc(sK1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1385]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1250,plain,
% 2.93/1.01      ( ~ r1_tarski(X0,u1_pre_topc(sK1))
% 2.93/1.01      | ~ r1_tarski(u1_pre_topc(sK1),X0)
% 2.93/1.01      | u1_pre_topc(sK1) = X0 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1526,plain,
% 2.93/1.01      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK1))
% 2.93/1.01      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
% 2.93/1.01      | u1_pre_topc(sK1) = u1_pre_topc(X0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1250]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1532,plain,
% 2.93/1.01      ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
% 2.93/1.01      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
% 2.93/1.01      | u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1526]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_525,plain,( X0 = X0 ),theory(equality) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1440,plain,
% 2.93/1.01      ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_525]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1421,plain,
% 2.93/1.01      ( sK1 = sK1 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_525]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_531,plain,
% 2.93/1.01      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 2.93/1.01      theory(equality) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1258,plain,
% 2.93/1.01      ( u1_pre_topc(sK1) = u1_pre_topc(X0) | sK1 != X0 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_531]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1420,plain,
% 2.93/1.01      ( u1_pre_topc(sK1) = u1_pre_topc(sK1) | sK1 != sK1 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1258]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_534,plain,
% 2.93/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.93/1.01      theory(equality) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1232,plain,
% 2.93/1.01      ( m1_subset_1(X0,X1)
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 2.93/1.01      | X1 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
% 2.93/1.01      | X0 != u1_pre_topc(X2) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_534]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1315,plain,
% 2.93/1.01      ( m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),X0)
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | X0 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1232]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1363,plain,
% 2.93/1.01      ( m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 2.93/1.01      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1315]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1366,plain,
% 2.93/1.01      ( m1_subset_1(k9_setfam_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 2.93/1.01      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1363]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_536,plain,
% 2.93/1.01      ( ~ v1_tops_2(X0,X1) | v1_tops_2(X2,X1) | X2 != X0 ),
% 2.93/1.01      theory(equality) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1208,plain,
% 2.93/1.01      ( v1_tops_2(X0,X1)
% 2.93/1.01      | ~ v1_tops_2(u1_pre_topc(X1),X1)
% 2.93/1.01      | X0 != u1_pre_topc(X1) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_536]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_1274,plain,
% 2.93/1.01      ( v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK0)
% 2.93/1.01      | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK0)) != u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_1208]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_542,plain,
% 2.93/1.01      ( u1_pre_topc(sK0) = u1_pre_topc(sK0) | sK0 != sK0 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_531]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_23,plain,
% 2.93/1.01      ( v1_tdlat_3(X0)
% 2.93/1.01      | ~ l1_pre_topc(X0)
% 2.93/1.01      | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_25,negated_conjecture,
% 2.93/1.01      ( ~ v1_tdlat_3(sK1) ),
% 2.93/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_329,plain,
% 2.93/1.01      ( ~ l1_pre_topc(X0)
% 2.93/1.01      | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)
% 2.93/1.01      | sK1 != X0 ),
% 2.93/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_330,plain,
% 2.93/1.01      ( ~ l1_pre_topc(sK1)
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
% 2.93/1.01      inference(unflattening,[status(thm)],[c_329]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_87,plain,
% 2.93/1.01      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_2,plain,
% 2.93/1.01      ( r1_tarski(X0,X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_83,plain,
% 2.93/1.01      ( r1_tarski(sK0,sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_78,plain,
% 2.93/1.01      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.93/1.01      | ~ l1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_59,plain,
% 2.93/1.01      ( v1_tops_2(u1_pre_topc(sK0),sK0) | ~ l1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_47,plain,
% 2.93/1.01      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_22,plain,
% 2.93/1.01      ( ~ v1_tdlat_3(X0) | ~ l1_pre_topc(X0) | v2_pre_topc(X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_39,plain,
% 2.93/1.01      ( ~ v1_tdlat_3(sK0) | ~ l1_pre_topc(sK0) | v2_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_24,plain,
% 2.93/1.01      ( ~ v1_tdlat_3(X0)
% 2.93/1.01      | ~ l1_pre_topc(X0)
% 2.93/1.01      | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_35,plain,
% 2.93/1.01      ( ~ v1_tdlat_3(sK0)
% 2.93/1.01      | ~ l1_pre_topc(sK0)
% 2.93/1.01      | k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 2.93/1.01      inference(instantiation,[status(thm)],[c_24]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(c_26,negated_conjecture,
% 2.93/1.01      ( v1_tdlat_3(sK0) ),
% 2.93/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.93/1.01  
% 2.93/1.01  cnf(contradiction,plain,
% 2.93/1.01      ( $false ),
% 2.93/1.01      inference(minisat,
% 2.93/1.01                [status(thm)],
% 2.93/1.01                [c_12087,c_10034,c_9537,c_6620,c_5850,c_4924,c_4406,
% 2.93/1.01                 c_4002,c_3781,c_2993,c_2939,c_2938,c_2422,c_2283,c_2024,
% 2.93/1.01                 c_2019,c_1914,c_1664,c_1532,c_1440,c_1421,c_1420,c_1366,
% 2.93/1.01                 c_1274,c_542,c_330,c_87,c_83,c_78,c_59,c_47,c_39,c_35,
% 2.93/1.01                 c_26,c_28,c_29]) ).
% 2.93/1.01  
% 2.93/1.01  
% 2.93/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/1.01  
% 2.93/1.01  ------                               Statistics
% 2.93/1.01  
% 2.93/1.01  ------ General
% 2.93/1.01  
% 2.93/1.01  abstr_ref_over_cycles:                  0
% 2.93/1.01  abstr_ref_under_cycles:                 0
% 2.93/1.01  gc_basic_clause_elim:                   0
% 2.93/1.01  forced_gc_time:                         0
% 2.93/1.01  parsing_time:                           0.013
% 2.93/1.01  unif_index_cands_time:                  0.
% 2.93/1.01  unif_index_add_time:                    0.
% 2.93/1.01  orderings_time:                         0.
% 2.93/1.01  out_proof_time:                         0.01
% 2.93/1.01  total_time:                             0.296
% 2.93/1.01  num_of_symbols:                         45
% 2.93/1.01  num_of_terms:                           2742
% 2.93/1.01  
% 2.93/1.01  ------ Preprocessing
% 2.93/1.01  
% 2.93/1.01  num_of_splits:                          0
% 2.93/1.01  num_of_split_atoms:                     0
% 2.93/1.01  num_of_reused_defs:                     0
% 2.93/1.01  num_eq_ax_congr_red:                    3
% 2.93/1.01  num_of_sem_filtered_clauses:            1
% 2.93/1.01  num_of_subtypes:                        0
% 2.93/1.01  monotx_restored_types:                  0
% 2.93/1.01  sat_num_of_epr_types:                   0
% 2.93/1.01  sat_num_of_non_cyclic_types:            0
% 2.93/1.01  sat_guarded_non_collapsed_types:        0
% 2.93/1.01  num_pure_diseq_elim:                    0
% 2.93/1.01  simp_replaced_by:                       0
% 2.93/1.01  res_preprocessed:                       135
% 2.93/1.01  prep_upred:                             0
% 2.93/1.01  prep_unflattend:                        3
% 2.93/1.01  smt_new_axioms:                         0
% 2.93/1.01  pred_elim_cands:                        6
% 2.93/1.01  pred_elim:                              1
% 2.93/1.01  pred_elim_cl:                           0
% 2.93/1.01  pred_elim_cycles:                       3
% 2.93/1.01  merged_defs:                            0
% 2.93/1.01  merged_defs_ncl:                        0
% 2.93/1.01  bin_hyper_res:                          0
% 2.93/1.01  prep_cycles:                            4
% 2.93/1.01  pred_elim_time:                         0.001
% 2.93/1.01  splitting_time:                         0.
% 2.93/1.01  sem_filter_time:                        0.
% 2.93/1.01  monotx_time:                            0.
% 2.93/1.01  subtype_inf_time:                       0.
% 2.93/1.01  
% 2.93/1.01  ------ Problem properties
% 2.93/1.01  
% 2.93/1.01  clauses:                                27
% 2.93/1.01  conjectures:                            3
% 2.93/1.01  epr:                                    10
% 2.93/1.01  horn:                                   27
% 2.93/1.01  ground:                                 7
% 2.93/1.01  unary:                                  8
% 2.93/1.01  binary:                                 3
% 2.93/1.01  lits:                                   80
% 2.93/1.01  lits_eq:                                6
% 2.93/1.01  fd_pure:                                0
% 2.93/1.01  fd_pseudo:                              0
% 2.93/1.01  fd_cond:                                0
% 2.93/1.01  fd_pseudo_cond:                         1
% 2.93/1.01  ac_symbols:                             0
% 2.93/1.01  
% 2.93/1.01  ------ Propositional Solver
% 2.93/1.01  
% 2.93/1.01  prop_solver_calls:                      30
% 2.93/1.01  prop_fast_solver_calls:                 1329
% 2.93/1.01  smt_solver_calls:                       0
% 2.93/1.01  smt_fast_solver_calls:                  0
% 2.93/1.01  prop_num_of_clauses:                    2629
% 2.93/1.01  prop_preprocess_simplified:             7604
% 2.93/1.01  prop_fo_subsumed:                       84
% 2.93/1.01  prop_solver_time:                       0.
% 2.93/1.01  smt_solver_time:                        0.
% 2.93/1.01  smt_fast_solver_time:                   0.
% 2.93/1.01  prop_fast_solver_time:                  0.
% 2.93/1.01  prop_unsat_core_time:                   0.
% 2.93/1.01  
% 2.93/1.01  ------ QBF
% 2.93/1.01  
% 2.93/1.01  qbf_q_res:                              0
% 2.93/1.01  qbf_num_tautologies:                    0
% 2.93/1.01  qbf_prep_cycles:                        0
% 2.93/1.01  
% 2.93/1.01  ------ BMC1
% 2.93/1.01  
% 2.93/1.01  bmc1_current_bound:                     -1
% 2.93/1.01  bmc1_last_solved_bound:                 -1
% 2.93/1.01  bmc1_unsat_core_size:                   -1
% 2.93/1.01  bmc1_unsat_core_parents_size:           -1
% 2.93/1.01  bmc1_merge_next_fun:                    0
% 2.93/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.93/1.01  
% 2.93/1.01  ------ Instantiation
% 2.93/1.01  
% 2.93/1.01  inst_num_of_clauses:                    673
% 2.93/1.01  inst_num_in_passive:                    136
% 2.93/1.01  inst_num_in_active:                     533
% 2.93/1.01  inst_num_in_unprocessed:                3
% 2.93/1.01  inst_num_of_loops:                      575
% 2.93/1.01  inst_num_of_learning_restarts:          0
% 2.93/1.01  inst_num_moves_active_passive:          34
% 2.93/1.01  inst_lit_activity:                      0
% 2.93/1.01  inst_lit_activity_moves:                0
% 2.93/1.01  inst_num_tautologies:                   0
% 2.93/1.01  inst_num_prop_implied:                  0
% 2.93/1.01  inst_num_existing_simplified:           0
% 2.93/1.01  inst_num_eq_res_simplified:             0
% 2.93/1.01  inst_num_child_elim:                    0
% 2.93/1.01  inst_num_of_dismatching_blockings:      754
% 2.93/1.01  inst_num_of_non_proper_insts:           1685
% 2.93/1.01  inst_num_of_duplicates:                 0
% 2.93/1.01  inst_inst_num_from_inst_to_res:         0
% 2.93/1.01  inst_dismatching_checking_time:         0.
% 2.93/1.01  
% 2.93/1.01  ------ Resolution
% 2.93/1.01  
% 2.93/1.01  res_num_of_clauses:                     0
% 2.93/1.01  res_num_in_passive:                     0
% 2.93/1.01  res_num_in_active:                      0
% 2.93/1.01  res_num_of_loops:                       139
% 2.93/1.01  res_forward_subset_subsumed:            270
% 2.93/1.01  res_backward_subset_subsumed:           8
% 2.93/1.01  res_forward_subsumed:                   0
% 2.93/1.01  res_backward_subsumed:                  0
% 2.93/1.01  res_forward_subsumption_resolution:     0
% 2.93/1.01  res_backward_subsumption_resolution:    0
% 2.93/1.01  res_clause_to_clause_subsumption:       3588
% 2.93/1.01  res_orphan_elimination:                 0
% 2.93/1.01  res_tautology_del:                      191
% 2.93/1.01  res_num_eq_res_simplified:              0
% 2.93/1.01  res_num_sel_changes:                    0
% 2.93/1.01  res_moves_from_active_to_pass:          0
% 2.93/1.01  
% 2.93/1.01  ------ Superposition
% 2.93/1.01  
% 2.93/1.01  sup_time_total:                         0.
% 2.93/1.01  sup_time_generating:                    0.
% 2.93/1.01  sup_time_sim_full:                      0.
% 2.93/1.01  sup_time_sim_immed:                     0.
% 2.93/1.01  
% 2.93/1.01  sup_num_of_clauses:                     327
% 2.93/1.01  sup_num_in_active:                      113
% 2.93/1.01  sup_num_in_passive:                     214
% 2.93/1.01  sup_num_of_loops:                       114
% 2.93/1.01  sup_fw_superposition:                   553
% 2.93/1.01  sup_bw_superposition:                   404
% 2.93/1.01  sup_immediate_simplified:               342
% 2.93/1.01  sup_given_eliminated:                   0
% 2.93/1.01  comparisons_done:                       0
% 2.93/1.01  comparisons_avoided:                    0
% 2.93/1.01  
% 2.93/1.01  ------ Simplifications
% 2.93/1.01  
% 2.93/1.01  
% 2.93/1.01  sim_fw_subset_subsumed:                 234
% 2.93/1.01  sim_bw_subset_subsumed:                 43
% 2.93/1.01  sim_fw_subsumed:                        72
% 2.93/1.01  sim_bw_subsumed:                        19
% 2.93/1.01  sim_fw_subsumption_res:                 7
% 2.93/1.01  sim_bw_subsumption_res:                 0
% 2.93/1.01  sim_tautology_del:                      49
% 2.93/1.01  sim_eq_tautology_del:                   2
% 2.93/1.01  sim_eq_res_simp:                        0
% 2.93/1.01  sim_fw_demodulated:                     0
% 2.93/1.01  sim_bw_demodulated:                     0
% 2.93/1.01  sim_light_normalised:                   31
% 2.93/1.01  sim_joinable_taut:                      0
% 2.93/1.01  sim_joinable_simp:                      0
% 2.93/1.01  sim_ac_normalised:                      0
% 2.93/1.01  sim_smt_subsumption:                    0
% 2.93/1.01  
%------------------------------------------------------------------------------
