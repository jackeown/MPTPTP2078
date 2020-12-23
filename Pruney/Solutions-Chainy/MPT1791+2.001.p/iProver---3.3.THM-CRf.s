%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:49 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  202 (4562 expanded)
%              Number of clauses        :  128 (1145 expanded)
%              Number of leaves         :   18 (1009 expanded)
%              Depth                    :   29
%              Number of atoms          :  726 (26553 expanded)
%              Number of equality atoms :  189 (5838 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1)
          | ~ v3_pre_topc(sK1,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f77,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_219,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_451,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_219])).

cnf(c_452,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_454,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_26,c_25])).

cnf(c_1215,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_26,c_25,c_452])).

cnf(c_2036,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_2040,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_779,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_780,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_784,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_27,c_26])).

cnf(c_2031,plain,
    ( k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
    | r2_hidden(X0,u1_pre_topc(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_2613,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_2031])).

cnf(c_2634,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2036,c_2613])).

cnf(c_14,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( m2_connsp_2(k2_struct_0(X0),X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | k2_struct_0(X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_15])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_526,c_28])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_27,c_26])).

cnf(c_2035,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_32,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2182,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_2183,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2182])).

cnf(c_2529,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2035,c_32,c_2183])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3010,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2529,c_2041])).

cnf(c_31,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2285,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2286,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2285])).

cnf(c_3467,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3010,c_31,c_32,c_2183,c_2286])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2044,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3472,plain,
    ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0)
    | r1_tarski(k2_struct_0(sK0),k1_tops_1(sK0,k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3467,c_2044])).

cnf(c_13,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m2_connsp_2(X0,X1,X2)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_171,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | r1_tarski(X0,k1_tops_1(X1,X4))
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | k2_struct_0(X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_171,c_15])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k1_tops_1(X1,k2_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k1_tops_1(X1,k2_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_505,c_28])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_27,c_26])).

cnf(c_2301,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_struct_0(sK0),k1_tops_1(sK0,k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_2465,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK0))
    | ~ r1_tarski(k2_struct_0(sK0),X0)
    | X0 = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2705,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ r1_tarski(k2_struct_0(sK0),k1_tops_1(sK0,k2_struct_0(sK0)))
    | k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_4272,plain,
    ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3472,c_26,c_25,c_2182,c_2285,c_2301,c_2705])).

cnf(c_2039,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_368,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_2038,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_3640,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2039,c_2038])).

cnf(c_4274,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4272,c_3640])).

cnf(c_10,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_416,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k1_tops_1(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_417,plain,
    ( r2_hidden(k1_tops_1(X0,X1),u1_pre_topc(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_925,plain,
    ( r2_hidden(k1_tops_1(X0,X1),u1_pre_topc(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_417,c_27])).

cnf(c_926,plain,
    ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_930,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_926,c_26])).

cnf(c_931,plain,
    ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_930])).

cnf(c_2027,plain,
    ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_4286,plain,
    ( r2_hidden(k1_tops_1(sK0,u1_struct_0(sK0)),u1_pre_topc(sK0)) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4274,c_2027])).

cnf(c_4299,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4286,c_4274])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2042,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2053,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2042,c_3])).

cnf(c_4738,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4299,c_2053])).

cnf(c_2615,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_2031])).

cnf(c_4740,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(superposition,[status(thm)],[c_4738,c_2615])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_821,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_826,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_27,c_26])).

cnf(c_904,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK0,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_826])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_857,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_858,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_909,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_27,c_26,c_858])).

cnf(c_2028,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_3627,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2053,c_2028])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_27,c_26])).

cnf(c_2032,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_2422,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2053,c_2032])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_27,c_26])).

cnf(c_2033,plain,
    ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_2423,plain,
    ( u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2053,c_2033])).

cnf(c_3629,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK0))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_3627,c_2422,c_2423])).

cnf(c_4836,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_4740,c_3629])).

cnf(c_5318,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | k6_tmap_1(sK0,u1_struct_0(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2634,c_4836])).

cnf(c_4837,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_4740,c_2422])).

cnf(c_5325,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) = u1_pre_topc(sK0) ),
    inference(superposition,[status(thm)],[c_5318,c_4837])).

cnf(c_2326,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2040,c_2032])).

cnf(c_5341,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_5325,c_2326])).

cnf(c_3625,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2040,c_2028])).

cnf(c_2273,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2040,c_2033])).

cnf(c_3635,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3625,c_2273,c_2326])).

cnf(c_5407,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5341,c_3635])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_217,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_437,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_217])).

cnf(c_438,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_440,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_26,c_25])).

cnf(c_19,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_800,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_801,plain,
    ( r2_hidden(X0,u1_pre_topc(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_805,plain,
    ( r2_hidden(X0,u1_pre_topc(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_27,c_26])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_440,c_805])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_1044])).

cnf(c_1047,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1045,c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5407,c_5341,c_1047])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n015.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:19:08 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.00/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/0.92  
% 3.00/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.92  
% 3.00/0.92  ------  iProver source info
% 3.00/0.92  
% 3.00/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.92  git: non_committed_changes: false
% 3.00/0.92  git: last_make_outside_of_git: false
% 3.00/0.92  
% 3.00/0.92  ------ 
% 3.00/0.92  
% 3.00/0.92  ------ Input Options
% 3.00/0.92  
% 3.00/0.92  --out_options                           all
% 3.00/0.92  --tptp_safe_out                         true
% 3.00/0.92  --problem_path                          ""
% 3.00/0.92  --include_path                          ""
% 3.00/0.92  --clausifier                            res/vclausify_rel
% 3.00/0.92  --clausifier_options                    --mode clausify
% 3.00/0.92  --stdin                                 false
% 3.00/0.92  --stats_out                             all
% 3.00/0.92  
% 3.00/0.92  ------ General Options
% 3.00/0.92  
% 3.00/0.92  --fof                                   false
% 3.00/0.92  --time_out_real                         305.
% 3.00/0.92  --time_out_virtual                      -1.
% 3.00/0.92  --symbol_type_check                     false
% 3.00/0.92  --clausify_out                          false
% 3.00/0.92  --sig_cnt_out                           false
% 3.00/0.92  --trig_cnt_out                          false
% 3.00/0.92  --trig_cnt_out_tolerance                1.
% 3.00/0.92  --trig_cnt_out_sk_spl                   false
% 3.00/0.92  --abstr_cl_out                          false
% 3.00/0.92  
% 3.00/0.92  ------ Global Options
% 3.00/0.92  
% 3.00/0.92  --schedule                              default
% 3.00/0.92  --add_important_lit                     false
% 3.00/0.92  --prop_solver_per_cl                    1000
% 3.00/0.92  --min_unsat_core                        false
% 3.00/0.92  --soft_assumptions                      false
% 3.00/0.92  --soft_lemma_size                       3
% 3.00/0.92  --prop_impl_unit_size                   0
% 3.00/0.92  --prop_impl_unit                        []
% 3.00/0.92  --share_sel_clauses                     true
% 3.00/0.92  --reset_solvers                         false
% 3.00/0.92  --bc_imp_inh                            [conj_cone]
% 3.00/0.92  --conj_cone_tolerance                   3.
% 3.00/0.92  --extra_neg_conj                        none
% 3.00/0.92  --large_theory_mode                     true
% 3.00/0.92  --prolific_symb_bound                   200
% 3.00/0.92  --lt_threshold                          2000
% 3.00/0.92  --clause_weak_htbl                      true
% 3.00/0.92  --gc_record_bc_elim                     false
% 3.00/0.92  
% 3.00/0.92  ------ Preprocessing Options
% 3.00/0.92  
% 3.00/0.92  --preprocessing_flag                    true
% 3.00/0.92  --time_out_prep_mult                    0.1
% 3.00/0.92  --splitting_mode                        input
% 3.00/0.92  --splitting_grd                         true
% 3.00/0.92  --splitting_cvd                         false
% 3.00/0.92  --splitting_cvd_svl                     false
% 3.00/0.92  --splitting_nvd                         32
% 3.00/0.92  --sub_typing                            true
% 3.00/0.92  --prep_gs_sim                           true
% 3.00/0.92  --prep_unflatten                        true
% 3.00/0.92  --prep_res_sim                          true
% 3.00/0.92  --prep_upred                            true
% 3.00/0.92  --prep_sem_filter                       exhaustive
% 3.00/0.92  --prep_sem_filter_out                   false
% 3.00/0.92  --pred_elim                             true
% 3.00/0.92  --res_sim_input                         true
% 3.00/0.92  --eq_ax_congr_red                       true
% 3.00/0.92  --pure_diseq_elim                       true
% 3.00/0.92  --brand_transform                       false
% 3.00/0.92  --non_eq_to_eq                          false
% 3.00/0.92  --prep_def_merge                        true
% 3.00/0.92  --prep_def_merge_prop_impl              false
% 3.00/0.92  --prep_def_merge_mbd                    true
% 3.00/0.92  --prep_def_merge_tr_red                 false
% 3.00/0.92  --prep_def_merge_tr_cl                  false
% 3.00/0.92  --smt_preprocessing                     true
% 3.00/0.92  --smt_ac_axioms                         fast
% 3.00/0.92  --preprocessed_out                      false
% 3.00/0.92  --preprocessed_stats                    false
% 3.00/0.92  
% 3.00/0.92  ------ Abstraction refinement Options
% 3.00/0.92  
% 3.00/0.92  --abstr_ref                             []
% 3.00/0.92  --abstr_ref_prep                        false
% 3.00/0.92  --abstr_ref_until_sat                   false
% 3.00/0.92  --abstr_ref_sig_restrict                funpre
% 3.00/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.92  --abstr_ref_under                       []
% 3.00/0.92  
% 3.00/0.92  ------ SAT Options
% 3.00/0.92  
% 3.00/0.92  --sat_mode                              false
% 3.00/0.92  --sat_fm_restart_options                ""
% 3.00/0.92  --sat_gr_def                            false
% 3.00/0.92  --sat_epr_types                         true
% 3.00/0.92  --sat_non_cyclic_types                  false
% 3.00/0.92  --sat_finite_models                     false
% 3.00/0.92  --sat_fm_lemmas                         false
% 3.00/0.92  --sat_fm_prep                           false
% 3.00/0.92  --sat_fm_uc_incr                        true
% 3.00/0.92  --sat_out_model                         small
% 3.00/0.92  --sat_out_clauses                       false
% 3.00/0.92  
% 3.00/0.92  ------ QBF Options
% 3.00/0.92  
% 3.00/0.92  --qbf_mode                              false
% 3.00/0.92  --qbf_elim_univ                         false
% 3.00/0.92  --qbf_dom_inst                          none
% 3.00/0.92  --qbf_dom_pre_inst                      false
% 3.00/0.92  --qbf_sk_in                             false
% 3.00/0.92  --qbf_pred_elim                         true
% 3.00/0.92  --qbf_split                             512
% 3.00/0.92  
% 3.00/0.92  ------ BMC1 Options
% 3.00/0.92  
% 3.00/0.92  --bmc1_incremental                      false
% 3.00/0.92  --bmc1_axioms                           reachable_all
% 3.00/0.92  --bmc1_min_bound                        0
% 3.00/0.92  --bmc1_max_bound                        -1
% 3.00/0.92  --bmc1_max_bound_default                -1
% 3.00/0.92  --bmc1_symbol_reachability              true
% 3.00/0.92  --bmc1_property_lemmas                  false
% 3.00/0.92  --bmc1_k_induction                      false
% 3.00/0.92  --bmc1_non_equiv_states                 false
% 3.00/0.92  --bmc1_deadlock                         false
% 3.00/0.92  --bmc1_ucm                              false
% 3.00/0.92  --bmc1_add_unsat_core                   none
% 3.00/0.92  --bmc1_unsat_core_children              false
% 3.00/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.92  --bmc1_out_stat                         full
% 3.00/0.92  --bmc1_ground_init                      false
% 3.00/0.92  --bmc1_pre_inst_next_state              false
% 3.00/0.92  --bmc1_pre_inst_state                   false
% 3.00/0.92  --bmc1_pre_inst_reach_state             false
% 3.00/0.92  --bmc1_out_unsat_core                   false
% 3.00/0.92  --bmc1_aig_witness_out                  false
% 3.00/0.92  --bmc1_verbose                          false
% 3.00/0.92  --bmc1_dump_clauses_tptp                false
% 3.00/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.92  --bmc1_dump_file                        -
% 3.00/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.92  --bmc1_ucm_extend_mode                  1
% 3.00/0.92  --bmc1_ucm_init_mode                    2
% 3.00/0.92  --bmc1_ucm_cone_mode                    none
% 3.00/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.92  --bmc1_ucm_relax_model                  4
% 3.00/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.92  --bmc1_ucm_layered_model                none
% 3.00/0.92  --bmc1_ucm_max_lemma_size               10
% 3.00/0.92  
% 3.00/0.92  ------ AIG Options
% 3.00/0.92  
% 3.00/0.92  --aig_mode                              false
% 3.00/0.92  
% 3.00/0.92  ------ Instantiation Options
% 3.00/0.92  
% 3.00/0.92  --instantiation_flag                    true
% 3.00/0.92  --inst_sos_flag                         false
% 3.00/0.92  --inst_sos_phase                        true
% 3.00/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.92  --inst_lit_sel_side                     num_symb
% 3.00/0.92  --inst_solver_per_active                1400
% 3.00/0.92  --inst_solver_calls_frac                1.
% 3.00/0.92  --inst_passive_queue_type               priority_queues
% 3.00/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.92  --inst_passive_queues_freq              [25;2]
% 3.00/0.92  --inst_dismatching                      true
% 3.00/0.92  --inst_eager_unprocessed_to_passive     true
% 3.00/0.92  --inst_prop_sim_given                   true
% 3.00/0.92  --inst_prop_sim_new                     false
% 3.00/0.92  --inst_subs_new                         false
% 3.00/0.92  --inst_eq_res_simp                      false
% 3.00/0.92  --inst_subs_given                       false
% 3.00/0.92  --inst_orphan_elimination               true
% 3.00/0.92  --inst_learning_loop_flag               true
% 3.00/0.92  --inst_learning_start                   3000
% 3.00/0.92  --inst_learning_factor                  2
% 3.00/0.92  --inst_start_prop_sim_after_learn       3
% 3.00/0.92  --inst_sel_renew                        solver
% 3.00/0.92  --inst_lit_activity_flag                true
% 3.00/0.92  --inst_restr_to_given                   false
% 3.00/0.92  --inst_activity_threshold               500
% 3.00/0.92  --inst_out_proof                        true
% 3.00/0.92  
% 3.00/0.92  ------ Resolution Options
% 3.00/0.92  
% 3.00/0.92  --resolution_flag                       true
% 3.00/0.92  --res_lit_sel                           adaptive
% 3.00/0.92  --res_lit_sel_side                      none
% 3.00/0.92  --res_ordering                          kbo
% 3.00/0.92  --res_to_prop_solver                    active
% 3.00/0.92  --res_prop_simpl_new                    false
% 3.00/0.92  --res_prop_simpl_given                  true
% 3.00/0.92  --res_passive_queue_type                priority_queues
% 3.00/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.92  --res_passive_queues_freq               [15;5]
% 3.00/0.92  --res_forward_subs                      full
% 3.00/0.92  --res_backward_subs                     full
% 3.00/0.92  --res_forward_subs_resolution           true
% 3.00/0.92  --res_backward_subs_resolution          true
% 3.00/0.92  --res_orphan_elimination                true
% 3.00/0.92  --res_time_limit                        2.
% 3.00/0.92  --res_out_proof                         true
% 3.00/0.92  
% 3.00/0.92  ------ Superposition Options
% 3.00/0.92  
% 3.00/0.92  --superposition_flag                    true
% 3.00/0.92  --sup_passive_queue_type                priority_queues
% 3.00/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.92  --demod_completeness_check              fast
% 3.00/0.92  --demod_use_ground                      true
% 3.00/0.92  --sup_to_prop_solver                    passive
% 3.00/0.92  --sup_prop_simpl_new                    true
% 3.00/0.92  --sup_prop_simpl_given                  true
% 3.00/0.92  --sup_fun_splitting                     false
% 3.00/0.92  --sup_smt_interval                      50000
% 3.00/0.92  
% 3.00/0.92  ------ Superposition Simplification Setup
% 3.00/0.92  
% 3.00/0.92  --sup_indices_passive                   []
% 3.00/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.92  --sup_full_bw                           [BwDemod]
% 3.00/0.92  --sup_immed_triv                        [TrivRules]
% 3.00/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.92  --sup_immed_bw_main                     []
% 3.00/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.92  
% 3.00/0.92  ------ Combination Options
% 3.00/0.92  
% 3.00/0.92  --comb_res_mult                         3
% 3.00/0.92  --comb_sup_mult                         2
% 3.00/0.92  --comb_inst_mult                        10
% 3.00/0.92  
% 3.00/0.92  ------ Debug Options
% 3.00/0.92  
% 3.00/0.92  --dbg_backtrace                         false
% 3.00/0.92  --dbg_dump_prop_clauses                 false
% 3.00/0.92  --dbg_dump_prop_clauses_file            -
% 3.00/0.92  --dbg_out_stat                          false
% 3.00/0.92  ------ Parsing...
% 3.00/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.92  
% 3.00/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.00/0.92  
% 3.00/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.92  
% 3.00/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.92  ------ Proving...
% 3.00/0.92  ------ Problem Properties 
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  clauses                                 21
% 3.00/0.92  conjectures                             2
% 3.00/0.92  EPR                                     3
% 3.00/0.92  Horn                                    20
% 3.00/0.92  unary                                   5
% 3.00/0.92  binary                                  9
% 3.00/0.92  lits                                    45
% 3.00/0.92  lits eq                                 11
% 3.00/0.92  fd_pure                                 0
% 3.00/0.92  fd_pseudo                               0
% 3.00/0.92  fd_cond                                 0
% 3.00/0.92  fd_pseudo_cond                          1
% 3.00/0.92  AC symbols                              0
% 3.00/0.92  
% 3.00/0.92  ------ Schedule dynamic 5 is on 
% 3.00/0.92  
% 3.00/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  ------ 
% 3.00/0.92  Current options:
% 3.00/0.92  ------ 
% 3.00/0.92  
% 3.00/0.92  ------ Input Options
% 3.00/0.92  
% 3.00/0.92  --out_options                           all
% 3.00/0.92  --tptp_safe_out                         true
% 3.00/0.92  --problem_path                          ""
% 3.00/0.92  --include_path                          ""
% 3.00/0.92  --clausifier                            res/vclausify_rel
% 3.00/0.92  --clausifier_options                    --mode clausify
% 3.00/0.92  --stdin                                 false
% 3.00/0.92  --stats_out                             all
% 3.00/0.92  
% 3.00/0.92  ------ General Options
% 3.00/0.92  
% 3.00/0.92  --fof                                   false
% 3.00/0.92  --time_out_real                         305.
% 3.00/0.92  --time_out_virtual                      -1.
% 3.00/0.92  --symbol_type_check                     false
% 3.00/0.92  --clausify_out                          false
% 3.00/0.92  --sig_cnt_out                           false
% 3.00/0.92  --trig_cnt_out                          false
% 3.00/0.92  --trig_cnt_out_tolerance                1.
% 3.00/0.92  --trig_cnt_out_sk_spl                   false
% 3.00/0.92  --abstr_cl_out                          false
% 3.00/0.92  
% 3.00/0.92  ------ Global Options
% 3.00/0.92  
% 3.00/0.92  --schedule                              default
% 3.00/0.92  --add_important_lit                     false
% 3.00/0.92  --prop_solver_per_cl                    1000
% 3.00/0.92  --min_unsat_core                        false
% 3.00/0.92  --soft_assumptions                      false
% 3.00/0.92  --soft_lemma_size                       3
% 3.00/0.92  --prop_impl_unit_size                   0
% 3.00/0.92  --prop_impl_unit                        []
% 3.00/0.92  --share_sel_clauses                     true
% 3.00/0.92  --reset_solvers                         false
% 3.00/0.92  --bc_imp_inh                            [conj_cone]
% 3.00/0.92  --conj_cone_tolerance                   3.
% 3.00/0.92  --extra_neg_conj                        none
% 3.00/0.92  --large_theory_mode                     true
% 3.00/0.92  --prolific_symb_bound                   200
% 3.00/0.92  --lt_threshold                          2000
% 3.00/0.92  --clause_weak_htbl                      true
% 3.00/0.92  --gc_record_bc_elim                     false
% 3.00/0.92  
% 3.00/0.92  ------ Preprocessing Options
% 3.00/0.92  
% 3.00/0.92  --preprocessing_flag                    true
% 3.00/0.92  --time_out_prep_mult                    0.1
% 3.00/0.92  --splitting_mode                        input
% 3.00/0.92  --splitting_grd                         true
% 3.00/0.92  --splitting_cvd                         false
% 3.00/0.92  --splitting_cvd_svl                     false
% 3.00/0.92  --splitting_nvd                         32
% 3.00/0.92  --sub_typing                            true
% 3.00/0.92  --prep_gs_sim                           true
% 3.00/0.92  --prep_unflatten                        true
% 3.00/0.92  --prep_res_sim                          true
% 3.00/0.92  --prep_upred                            true
% 3.00/0.92  --prep_sem_filter                       exhaustive
% 3.00/0.92  --prep_sem_filter_out                   false
% 3.00/0.92  --pred_elim                             true
% 3.00/0.92  --res_sim_input                         true
% 3.00/0.92  --eq_ax_congr_red                       true
% 3.00/0.92  --pure_diseq_elim                       true
% 3.00/0.92  --brand_transform                       false
% 3.00/0.92  --non_eq_to_eq                          false
% 3.00/0.92  --prep_def_merge                        true
% 3.00/0.92  --prep_def_merge_prop_impl              false
% 3.00/0.92  --prep_def_merge_mbd                    true
% 3.00/0.92  --prep_def_merge_tr_red                 false
% 3.00/0.92  --prep_def_merge_tr_cl                  false
% 3.00/0.92  --smt_preprocessing                     true
% 3.00/0.92  --smt_ac_axioms                         fast
% 3.00/0.92  --preprocessed_out                      false
% 3.00/0.92  --preprocessed_stats                    false
% 3.00/0.92  
% 3.00/0.92  ------ Abstraction refinement Options
% 3.00/0.92  
% 3.00/0.92  --abstr_ref                             []
% 3.00/0.92  --abstr_ref_prep                        false
% 3.00/0.92  --abstr_ref_until_sat                   false
% 3.00/0.92  --abstr_ref_sig_restrict                funpre
% 3.00/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.92  --abstr_ref_under                       []
% 3.00/0.92  
% 3.00/0.92  ------ SAT Options
% 3.00/0.92  
% 3.00/0.92  --sat_mode                              false
% 3.00/0.92  --sat_fm_restart_options                ""
% 3.00/0.92  --sat_gr_def                            false
% 3.00/0.92  --sat_epr_types                         true
% 3.00/0.92  --sat_non_cyclic_types                  false
% 3.00/0.92  --sat_finite_models                     false
% 3.00/0.92  --sat_fm_lemmas                         false
% 3.00/0.92  --sat_fm_prep                           false
% 3.00/0.92  --sat_fm_uc_incr                        true
% 3.00/0.92  --sat_out_model                         small
% 3.00/0.92  --sat_out_clauses                       false
% 3.00/0.92  
% 3.00/0.92  ------ QBF Options
% 3.00/0.92  
% 3.00/0.92  --qbf_mode                              false
% 3.00/0.92  --qbf_elim_univ                         false
% 3.00/0.92  --qbf_dom_inst                          none
% 3.00/0.92  --qbf_dom_pre_inst                      false
% 3.00/0.92  --qbf_sk_in                             false
% 3.00/0.92  --qbf_pred_elim                         true
% 3.00/0.92  --qbf_split                             512
% 3.00/0.92  
% 3.00/0.92  ------ BMC1 Options
% 3.00/0.92  
% 3.00/0.92  --bmc1_incremental                      false
% 3.00/0.92  --bmc1_axioms                           reachable_all
% 3.00/0.92  --bmc1_min_bound                        0
% 3.00/0.92  --bmc1_max_bound                        -1
% 3.00/0.92  --bmc1_max_bound_default                -1
% 3.00/0.92  --bmc1_symbol_reachability              true
% 3.00/0.92  --bmc1_property_lemmas                  false
% 3.00/0.92  --bmc1_k_induction                      false
% 3.00/0.92  --bmc1_non_equiv_states                 false
% 3.00/0.92  --bmc1_deadlock                         false
% 3.00/0.92  --bmc1_ucm                              false
% 3.00/0.92  --bmc1_add_unsat_core                   none
% 3.00/0.92  --bmc1_unsat_core_children              false
% 3.00/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.92  --bmc1_out_stat                         full
% 3.00/0.92  --bmc1_ground_init                      false
% 3.00/0.92  --bmc1_pre_inst_next_state              false
% 3.00/0.92  --bmc1_pre_inst_state                   false
% 3.00/0.92  --bmc1_pre_inst_reach_state             false
% 3.00/0.92  --bmc1_out_unsat_core                   false
% 3.00/0.92  --bmc1_aig_witness_out                  false
% 3.00/0.92  --bmc1_verbose                          false
% 3.00/0.92  --bmc1_dump_clauses_tptp                false
% 3.00/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.92  --bmc1_dump_file                        -
% 3.00/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.92  --bmc1_ucm_extend_mode                  1
% 3.00/0.92  --bmc1_ucm_init_mode                    2
% 3.00/0.92  --bmc1_ucm_cone_mode                    none
% 3.00/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.92  --bmc1_ucm_relax_model                  4
% 3.00/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.92  --bmc1_ucm_layered_model                none
% 3.00/0.92  --bmc1_ucm_max_lemma_size               10
% 3.00/0.92  
% 3.00/0.92  ------ AIG Options
% 3.00/0.92  
% 3.00/0.92  --aig_mode                              false
% 3.00/0.92  
% 3.00/0.92  ------ Instantiation Options
% 3.00/0.92  
% 3.00/0.92  --instantiation_flag                    true
% 3.00/0.92  --inst_sos_flag                         false
% 3.00/0.92  --inst_sos_phase                        true
% 3.00/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.92  --inst_lit_sel_side                     none
% 3.00/0.92  --inst_solver_per_active                1400
% 3.00/0.92  --inst_solver_calls_frac                1.
% 3.00/0.92  --inst_passive_queue_type               priority_queues
% 3.00/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.92  --inst_passive_queues_freq              [25;2]
% 3.00/0.92  --inst_dismatching                      true
% 3.00/0.92  --inst_eager_unprocessed_to_passive     true
% 3.00/0.92  --inst_prop_sim_given                   true
% 3.00/0.92  --inst_prop_sim_new                     false
% 3.00/0.92  --inst_subs_new                         false
% 3.00/0.92  --inst_eq_res_simp                      false
% 3.00/0.92  --inst_subs_given                       false
% 3.00/0.92  --inst_orphan_elimination               true
% 3.00/0.92  --inst_learning_loop_flag               true
% 3.00/0.92  --inst_learning_start                   3000
% 3.00/0.92  --inst_learning_factor                  2
% 3.00/0.92  --inst_start_prop_sim_after_learn       3
% 3.00/0.92  --inst_sel_renew                        solver
% 3.00/0.92  --inst_lit_activity_flag                true
% 3.00/0.92  --inst_restr_to_given                   false
% 3.00/0.92  --inst_activity_threshold               500
% 3.00/0.92  --inst_out_proof                        true
% 3.00/0.92  
% 3.00/0.92  ------ Resolution Options
% 3.00/0.92  
% 3.00/0.92  --resolution_flag                       false
% 3.00/0.92  --res_lit_sel                           adaptive
% 3.00/0.92  --res_lit_sel_side                      none
% 3.00/0.92  --res_ordering                          kbo
% 3.00/0.92  --res_to_prop_solver                    active
% 3.00/0.92  --res_prop_simpl_new                    false
% 3.00/0.92  --res_prop_simpl_given                  true
% 3.00/0.92  --res_passive_queue_type                priority_queues
% 3.00/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.92  --res_passive_queues_freq               [15;5]
% 3.00/0.92  --res_forward_subs                      full
% 3.00/0.92  --res_backward_subs                     full
% 3.00/0.92  --res_forward_subs_resolution           true
% 3.00/0.92  --res_backward_subs_resolution          true
% 3.00/0.92  --res_orphan_elimination                true
% 3.00/0.92  --res_time_limit                        2.
% 3.00/0.92  --res_out_proof                         true
% 3.00/0.92  
% 3.00/0.92  ------ Superposition Options
% 3.00/0.92  
% 3.00/0.92  --superposition_flag                    true
% 3.00/0.92  --sup_passive_queue_type                priority_queues
% 3.00/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.92  --demod_completeness_check              fast
% 3.00/0.92  --demod_use_ground                      true
% 3.00/0.92  --sup_to_prop_solver                    passive
% 3.00/0.92  --sup_prop_simpl_new                    true
% 3.00/0.92  --sup_prop_simpl_given                  true
% 3.00/0.92  --sup_fun_splitting                     false
% 3.00/0.92  --sup_smt_interval                      50000
% 3.00/0.92  
% 3.00/0.92  ------ Superposition Simplification Setup
% 3.00/0.92  
% 3.00/0.92  --sup_indices_passive                   []
% 3.00/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.92  --sup_full_bw                           [BwDemod]
% 3.00/0.92  --sup_immed_triv                        [TrivRules]
% 3.00/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.92  --sup_immed_bw_main                     []
% 3.00/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.92  
% 3.00/0.92  ------ Combination Options
% 3.00/0.92  
% 3.00/0.92  --comb_res_mult                         3
% 3.00/0.92  --comb_sup_mult                         2
% 3.00/0.92  --comb_inst_mult                        10
% 3.00/0.92  
% 3.00/0.92  ------ Debug Options
% 3.00/0.92  
% 3.00/0.92  --dbg_backtrace                         false
% 3.00/0.92  --dbg_dump_prop_clauses                 false
% 3.00/0.92  --dbg_dump_prop_clauses_file            -
% 3.00/0.92  --dbg_out_stat                          false
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  ------ Proving...
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  % SZS status Theorem for theBenchmark.p
% 3.00/0.92  
% 3.00/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.92  
% 3.00/0.92  fof(f6,axiom,(
% 3.00/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f21,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.00/0.92    inference(ennf_transformation,[],[f6])).
% 3.00/0.92  
% 3.00/0.92  fof(f42,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.00/0.92    inference(nnf_transformation,[],[f21])).
% 3.00/0.92  
% 3.00/0.92  fof(f57,plain,(
% 3.00/0.92    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f42])).
% 3.00/0.92  
% 3.00/0.92  fof(f16,conjecture,(
% 3.00/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f17,negated_conjecture,(
% 3.00/0.92    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 3.00/0.92    inference(negated_conjecture,[],[f16])).
% 3.00/0.92  
% 3.00/0.92  fof(f38,plain,(
% 3.00/0.92    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f17])).
% 3.00/0.92  
% 3.00/0.92  fof(f39,plain,(
% 3.00/0.92    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.00/0.92    inference(flattening,[],[f38])).
% 3.00/0.92  
% 3.00/0.92  fof(f45,plain,(
% 3.00/0.92    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.00/0.92    inference(nnf_transformation,[],[f39])).
% 3.00/0.92  
% 3.00/0.92  fof(f46,plain,(
% 3.00/0.92    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.00/0.92    inference(flattening,[],[f45])).
% 3.00/0.92  
% 3.00/0.92  fof(f48,plain,(
% 3.00/0.92    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.00/0.92    introduced(choice_axiom,[])).
% 3.00/0.92  
% 3.00/0.92  fof(f47,plain,(
% 3.00/0.92    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.00/0.92    introduced(choice_axiom,[])).
% 3.00/0.92  
% 3.00/0.92  fof(f49,plain,(
% 3.00/0.92    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.00/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).
% 3.00/0.92  
% 3.00/0.92  fof(f77,plain,(
% 3.00/0.92    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 3.00/0.92    inference(cnf_transformation,[],[f49])).
% 3.00/0.92  
% 3.00/0.92  fof(f75,plain,(
% 3.00/0.92    l1_pre_topc(sK0)),
% 3.00/0.92    inference(cnf_transformation,[],[f49])).
% 3.00/0.92  
% 3.00/0.92  fof(f76,plain,(
% 3.00/0.92    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.92    inference(cnf_transformation,[],[f49])).
% 3.00/0.92  
% 3.00/0.92  fof(f14,axiom,(
% 3.00/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f34,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f14])).
% 3.00/0.92  
% 3.00/0.92  fof(f35,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/0.92    inference(flattening,[],[f34])).
% 3.00/0.92  
% 3.00/0.92  fof(f44,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/0.92    inference(nnf_transformation,[],[f35])).
% 3.00/0.92  
% 3.00/0.92  fof(f69,plain,(
% 3.00/0.92    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f44])).
% 3.00/0.92  
% 3.00/0.92  fof(f73,plain,(
% 3.00/0.92    ~v2_struct_0(sK0)),
% 3.00/0.92    inference(cnf_transformation,[],[f49])).
% 3.00/0.92  
% 3.00/0.92  fof(f74,plain,(
% 3.00/0.92    v2_pre_topc(sK0)),
% 3.00/0.92    inference(cnf_transformation,[],[f49])).
% 3.00/0.92  
% 3.00/0.92  fof(f11,axiom,(
% 3.00/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f28,plain,(
% 3.00/0.92    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f11])).
% 3.00/0.92  
% 3.00/0.92  fof(f29,plain,(
% 3.00/0.92    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.00/0.92    inference(flattening,[],[f28])).
% 3.00/0.92  
% 3.00/0.92  fof(f64,plain,(
% 3.00/0.92    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f29])).
% 3.00/0.92  
% 3.00/0.92  fof(f12,axiom,(
% 3.00/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f30,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f12])).
% 3.00/0.92  
% 3.00/0.92  fof(f31,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/0.92    inference(flattening,[],[f30])).
% 3.00/0.92  
% 3.00/0.92  fof(f65,plain,(
% 3.00/0.92    ( ! [X0,X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f31])).
% 3.00/0.92  
% 3.00/0.92  fof(f9,axiom,(
% 3.00/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f25,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.00/0.92    inference(ennf_transformation,[],[f9])).
% 3.00/0.92  
% 3.00/0.92  fof(f61,plain,(
% 3.00/0.92    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f25])).
% 3.00/0.92  
% 3.00/0.92  fof(f1,axiom,(
% 3.00/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f40,plain,(
% 3.00/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.92    inference(nnf_transformation,[],[f1])).
% 3.00/0.92  
% 3.00/0.92  fof(f41,plain,(
% 3.00/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.92    inference(flattening,[],[f40])).
% 3.00/0.92  
% 3.00/0.92  fof(f52,plain,(
% 3.00/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f41])).
% 3.00/0.92  
% 3.00/0.92  fof(f10,axiom,(
% 3.00/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f26,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f10])).
% 3.00/0.92  
% 3.00/0.92  fof(f27,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.00/0.92    inference(flattening,[],[f26])).
% 3.00/0.92  
% 3.00/0.92  fof(f43,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.00/0.92    inference(nnf_transformation,[],[f27])).
% 3.00/0.92  
% 3.00/0.92  fof(f62,plain,(
% 3.00/0.92    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f43])).
% 3.00/0.92  
% 3.00/0.92  fof(f7,axiom,(
% 3.00/0.92    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f22,plain,(
% 3.00/0.92    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.00/0.92    inference(ennf_transformation,[],[f7])).
% 3.00/0.92  
% 3.00/0.92  fof(f59,plain,(
% 3.00/0.92    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f22])).
% 3.00/0.92  
% 3.00/0.92  fof(f5,axiom,(
% 3.00/0.92    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f20,plain,(
% 3.00/0.92    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.00/0.92    inference(ennf_transformation,[],[f5])).
% 3.00/0.92  
% 3.00/0.92  fof(f56,plain,(
% 3.00/0.92    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f20])).
% 3.00/0.92  
% 3.00/0.92  fof(f8,axiom,(
% 3.00/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f23,plain,(
% 3.00/0.92    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f8])).
% 3.00/0.92  
% 3.00/0.92  fof(f24,plain,(
% 3.00/0.92    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.00/0.92    inference(flattening,[],[f23])).
% 3.00/0.92  
% 3.00/0.92  fof(f60,plain,(
% 3.00/0.92    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f24])).
% 3.00/0.92  
% 3.00/0.92  fof(f3,axiom,(
% 3.00/0.92    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f54,plain,(
% 3.00/0.92    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.00/0.92    inference(cnf_transformation,[],[f3])).
% 3.00/0.92  
% 3.00/0.92  fof(f2,axiom,(
% 3.00/0.92    ! [X0] : k2_subset_1(X0) = X0),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f53,plain,(
% 3.00/0.92    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.00/0.92    inference(cnf_transformation,[],[f2])).
% 3.00/0.92  
% 3.00/0.92  fof(f4,axiom,(
% 3.00/0.92    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f18,plain,(
% 3.00/0.92    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.00/0.92    inference(ennf_transformation,[],[f4])).
% 3.00/0.92  
% 3.00/0.92  fof(f19,plain,(
% 3.00/0.92    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.00/0.92    inference(flattening,[],[f18])).
% 3.00/0.92  
% 3.00/0.92  fof(f55,plain,(
% 3.00/0.92    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f19])).
% 3.00/0.92  
% 3.00/0.92  fof(f13,axiom,(
% 3.00/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f32,plain,(
% 3.00/0.92    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f13])).
% 3.00/0.92  
% 3.00/0.92  fof(f33,plain,(
% 3.00/0.92    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/0.92    inference(flattening,[],[f32])).
% 3.00/0.92  
% 3.00/0.92  fof(f66,plain,(
% 3.00/0.92    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f33])).
% 3.00/0.92  
% 3.00/0.92  fof(f68,plain,(
% 3.00/0.92    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f33])).
% 3.00/0.92  
% 3.00/0.92  fof(f15,axiom,(
% 3.00/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.00/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.92  
% 3.00/0.92  fof(f36,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/0.92    inference(ennf_transformation,[],[f15])).
% 3.00/0.92  
% 3.00/0.92  fof(f37,plain,(
% 3.00/0.92    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/0.92    inference(flattening,[],[f36])).
% 3.00/0.92  
% 3.00/0.92  fof(f72,plain,(
% 3.00/0.92    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f37])).
% 3.00/0.92  
% 3.00/0.92  fof(f71,plain,(
% 3.00/0.92    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f37])).
% 3.00/0.92  
% 3.00/0.92  fof(f58,plain,(
% 3.00/0.92    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f42])).
% 3.00/0.92  
% 3.00/0.92  fof(f78,plain,(
% 3.00/0.92    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.00/0.92    inference(cnf_transformation,[],[f49])).
% 3.00/0.92  
% 3.00/0.92  fof(f70,plain,(
% 3.00/0.92    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/0.92    inference(cnf_transformation,[],[f44])).
% 3.00/0.92  
% 3.00/0.92  cnf(c_8,plain,
% 3.00/0.92      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ v3_pre_topc(X0,X1)
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f57]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_24,negated_conjecture,
% 3.00/0.92      ( v3_pre_topc(sK1,sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f77]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_219,plain,
% 3.00/0.92      ( v3_pre_topc(sK1,sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_451,plain,
% 3.00/0.92      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 3.00/0.92      | sK1 != X0
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_8,c_219]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_452,plain,
% 3.00/0.92      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ l1_pre_topc(sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_451]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_26,negated_conjecture,
% 3.00/0.92      ( l1_pre_topc(sK0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f75]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_25,negated_conjecture,
% 3.00/0.92      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.00/0.92      inference(cnf_transformation,[],[f76]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_454,plain,
% 3.00/0.92      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_452,c_26,c_25]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_1215,plain,
% 3.00/0.92      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(prop_impl,[status(thm)],[c_26,c_25,c_452]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2036,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 3.00/0.92      | r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_1215]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2040,plain,
% 3.00/0.92      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_20,plain,
% 3.00/0.92      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f69]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_28,negated_conjecture,
% 3.00/0.92      ( ~ v2_struct_0(sK0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f73]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_779,plain,
% 3.00/0.92      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_780,plain,
% 3.00/0.92      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | ~ l1_pre_topc(sK0)
% 3.00/0.92      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_779]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_27,negated_conjecture,
% 3.00/0.92      ( v2_pre_topc(sK0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f74]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_784,plain,
% 3.00/0.92      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_780,c_27,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2031,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
% 3.00/0.92      | r2_hidden(X0,u1_pre_topc(sK0)) != iProver_top
% 3.00/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2613,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 3.00/0.92      | r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2040,c_2031]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2634,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2036,c_2613]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_14,plain,
% 3.00/0.92      ( ~ m2_connsp_2(X0,X1,X2)
% 3.00/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f64]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_15,plain,
% 3.00/0.92      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
% 3.00/0.92      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/0.92      | v2_struct_0(X0)
% 3.00/0.92      | ~ v2_pre_topc(X0)
% 3.00/0.92      | ~ l1_pre_topc(X0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f65]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_525,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.00/0.92      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X3)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ v2_pre_topc(X3)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X3)
% 3.00/0.92      | X3 != X1
% 3.00/0.92      | X2 != X0
% 3.00/0.92      | k2_struct_0(X3) != X4 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_14,c_15]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_526,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_525]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_707,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_526,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_708,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | ~ l1_pre_topc(sK0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_707]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_712,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_708,c_27,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2035,plain,
% 3.00/0.92      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.00/0.92      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_32,plain,
% 3.00/0.92      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2182,plain,
% 3.00/0.92      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.00/0.92      inference(instantiation,[status(thm)],[c_712]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2183,plain,
% 3.00/0.92      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.00/0.92      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_2182]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2529,plain,
% 3.00/0.92      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_2035,c_32,c_2183]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_11,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f61]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2041,plain,
% 3.00/0.92      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.00/0.92      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 3.00/0.92      | l1_pre_topc(X1) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3010,plain,
% 3.00/0.92      ( r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top
% 3.00/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2529,c_2041]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_31,plain,
% 3.00/0.92      ( l1_pre_topc(sK0) = iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2285,plain,
% 3.00/0.92      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
% 3.00/0.92      | ~ l1_pre_topc(sK0) ),
% 3.00/0.92      inference(instantiation,[status(thm)],[c_11]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2286,plain,
% 3.00/0.92      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.00/0.92      | r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top
% 3.00/0.92      | l1_pre_topc(sK0) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_2285]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3467,plain,
% 3.00/0.92      ( r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_3010,c_31,c_32,c_2183,c_2286]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_0,plain,
% 3.00/0.92      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.00/0.92      inference(cnf_transformation,[],[f52]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2044,plain,
% 3.00/0.92      ( X0 = X1
% 3.00/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.00/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3472,plain,
% 3.00/0.92      ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0)
% 3.00/0.92      | r1_tarski(k2_struct_0(sK0),k1_tops_1(sK0,k2_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_3467,c_2044]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_13,plain,
% 3.00/0.92      ( ~ m2_connsp_2(X0,X1,X2)
% 3.00/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | r1_tarski(X2,k1_tops_1(X1,X0))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f62]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_170,plain,
% 3.00/0.92      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ m2_connsp_2(X0,X1,X2)
% 3.00/0.92      | r1_tarski(X2,k1_tops_1(X1,X0))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_13,c_14]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_171,plain,
% 3.00/0.92      ( ~ m2_connsp_2(X0,X1,X2)
% 3.00/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | r1_tarski(X2,k1_tops_1(X1,X0))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(renaming,[status(thm)],[c_170]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_504,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.00/0.92      | r1_tarski(X0,k1_tops_1(X1,X4))
% 3.00/0.92      | v2_struct_0(X3)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ v2_pre_topc(X3)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X3)
% 3.00/0.92      | X3 != X1
% 3.00/0.92      | X2 != X0
% 3.00/0.92      | k2_struct_0(X3) != X4 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_171,c_15]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_505,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | r1_tarski(X0,k1_tops_1(X1,k2_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_504]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_725,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | r1_tarski(X0,k1_tops_1(X1,k2_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_505,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_726,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | ~ l1_pre_topc(sK0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_725]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_730,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | r1_tarski(X0,k1_tops_1(sK0,k2_struct_0(sK0))) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_726,c_27,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2301,plain,
% 3.00/0.92      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | r1_tarski(k2_struct_0(sK0),k1_tops_1(sK0,k2_struct_0(sK0))) ),
% 3.00/0.92      inference(instantiation,[status(thm)],[c_730]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2465,plain,
% 3.00/0.92      ( ~ r1_tarski(X0,k2_struct_0(sK0))
% 3.00/0.92      | ~ r1_tarski(k2_struct_0(sK0),X0)
% 3.00/0.92      | X0 = k2_struct_0(sK0) ),
% 3.00/0.92      inference(instantiation,[status(thm)],[c_0]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2705,plain,
% 3.00/0.92      ( ~ r1_tarski(k1_tops_1(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
% 3.00/0.92      | ~ r1_tarski(k2_struct_0(sK0),k1_tops_1(sK0,k2_struct_0(sK0)))
% 3.00/0.92      | k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 3.00/0.92      inference(instantiation,[status(thm)],[c_2465]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4272,plain,
% 3.00/0.92      ( k1_tops_1(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_3472,c_26,c_25,c_2182,c_2285,c_2301,c_2705]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2039,plain,
% 3.00/0.92      ( l1_pre_topc(sK0) = iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_9,plain,
% 3.00/0.92      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f59]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_6,plain,
% 3.00/0.92      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f56]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_368,plain,
% 3.00/0.92      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.00/0.92      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2038,plain,
% 3.00/0.92      ( k2_struct_0(X0) = u1_struct_0(X0)
% 3.00/0.92      | l1_pre_topc(X0) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3640,plain,
% 3.00/0.92      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2039,c_2038]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4274,plain,
% 3.00/0.92      ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 3.00/0.92      inference(light_normalisation,[status(thm)],[c_4272,c_3640]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_10,plain,
% 3.00/0.92      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.00/0.92      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/0.92      | ~ v2_pre_topc(X0)
% 3.00/0.92      | ~ l1_pre_topc(X0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f60]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_416,plain,
% 3.00/0.92      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.00/0.92      | ~ v2_pre_topc(X3)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X3)
% 3.00/0.92      | X3 != X1
% 3.00/0.92      | k1_tops_1(X3,X2) != X0 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_417,plain,
% 3.00/0.92      ( r2_hidden(k1_tops_1(X0,X1),u1_pre_topc(X0))
% 3.00/0.92      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/0.92      | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/0.92      | ~ v2_pre_topc(X0)
% 3.00/0.92      | ~ l1_pre_topc(X0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_416]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_925,plain,
% 3.00/0.92      ( r2_hidden(k1_tops_1(X0,X1),u1_pre_topc(X0))
% 3.00/0.92      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/0.92      | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/0.92      | ~ l1_pre_topc(X0)
% 3.00/0.92      | sK0 != X0 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_417,c_27]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_926,plain,
% 3.00/0.92      ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ l1_pre_topc(sK0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_925]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_930,plain,
% 3.00/0.92      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0)) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_926,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_931,plain,
% 3.00/0.92      ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.00/0.92      inference(renaming,[status(thm)],[c_930]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2027,plain,
% 3.00/0.92      ( r2_hidden(k1_tops_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top
% 3.00/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.00/0.92      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4286,plain,
% 3.00/0.92      ( r2_hidden(k1_tops_1(sK0,u1_struct_0(sK0)),u1_pre_topc(sK0)) = iProver_top
% 3.00/0.92      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_4274,c_2027]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4299,plain,
% 3.00/0.92      ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) = iProver_top
% 3.00/0.92      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(light_normalisation,[status(thm)],[c_4286,c_4274]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4,plain,
% 3.00/0.92      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.00/0.92      inference(cnf_transformation,[],[f54]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2042,plain,
% 3.00/0.92      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3,plain,
% 3.00/0.92      ( k2_subset_1(X0) = X0 ),
% 3.00/0.92      inference(cnf_transformation,[],[f53]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2053,plain,
% 3.00/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/0.92      inference(light_normalisation,[status(thm)],[c_2042,c_3]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4738,plain,
% 3.00/0.92      ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) = iProver_top ),
% 3.00/0.92      inference(forward_subsumption_resolution,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_4299,c_2053]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2615,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0)
% 3.00/0.92      | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) != iProver_top ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2053,c_2031]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4740,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_4738,c_2615]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_5,plain,
% 3.00/0.92      ( ~ l1_pre_topc(X0)
% 3.00/0.92      | ~ v1_pre_topc(X0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.00/0.92      inference(cnf_transformation,[],[f55]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_18,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | v1_pre_topc(k6_tmap_1(X1,X0)) ),
% 3.00/0.92      inference(cnf_transformation,[],[f66]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_821,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | v1_pre_topc(k6_tmap_1(X1,X0))
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_822,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | ~ l1_pre_topc(sK0)
% 3.00/0.92      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_821]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_826,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_822,c_27,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_904,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | k6_tmap_1(sK0,X0) != X1
% 3.00/0.92      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_5,c_826]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_905,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
% 3.00/0.92      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_904]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_16,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 3.00/0.92      inference(cnf_transformation,[],[f68]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_857,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | l1_pre_topc(k6_tmap_1(X1,X0))
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_858,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | l1_pre_topc(k6_tmap_1(sK0,X0))
% 3.00/0.92      | ~ l1_pre_topc(sK0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_857]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_909,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_905,c_27,c_26,c_858]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2028,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0)
% 3.00/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3627,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2053,c_2028]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_21,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 3.00/0.92      inference(cnf_transformation,[],[f72]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_761,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_762,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | ~ l1_pre_topc(sK0)
% 3.00/0.92      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_761]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_766,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_762,c_27,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2032,plain,
% 3.00/0.92      ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
% 3.00/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2422,plain,
% 3.00/0.92      ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2053,c_2032]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_22,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f71]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_743,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_744,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | ~ l1_pre_topc(sK0)
% 3.00/0.92      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_743]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_748,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_744,c_27,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2033,plain,
% 3.00/0.92      ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
% 3.00/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.92      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2423,plain,
% 3.00/0.92      ( u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2053,c_2033]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3629,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK0))) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
% 3.00/0.92      inference(light_normalisation,[status(thm)],[c_3627,c_2422,c_2423]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4836,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
% 3.00/0.92      inference(demodulation,[status(thm)],[c_4740,c_3629]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_5318,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 3.00/0.92      | k6_tmap_1(sK0,u1_struct_0(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2634,c_4836]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_4837,plain,
% 3.00/0.92      ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) = u1_pre_topc(sK0) ),
% 3.00/0.92      inference(demodulation,[status(thm)],[c_4740,c_2422]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_5325,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 3.00/0.92      | u1_pre_topc(k6_tmap_1(sK0,sK1)) = u1_pre_topc(sK0) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_5318,c_4837]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2326,plain,
% 3.00/0.92      ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2040,c_2032]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_5341,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 3.00/0.92      inference(demodulation,[status(thm)],[c_5325,c_2326]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3625,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2040,c_2028]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_2273,plain,
% 3.00/0.92      ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
% 3.00/0.92      inference(superposition,[status(thm)],[c_2040,c_2033]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_3635,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(light_normalisation,[status(thm)],[c_3625,c_2273,c_2326]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_5407,plain,
% 3.00/0.92      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(demodulation,[status(thm)],[c_5341,c_3635]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_7,plain,
% 3.00/0.92      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | v3_pre_topc(X0,X1)
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ l1_pre_topc(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f58]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_23,negated_conjecture,
% 3.00/0.92      ( ~ v3_pre_topc(sK1,sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f78]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_217,plain,
% 3.00/0.92      ( ~ v3_pre_topc(sK1,sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_437,plain,
% 3.00/0.92      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 3.00/0.92      | sK1 != X0
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_7,c_217]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_438,plain,
% 3.00/0.92      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ l1_pre_topc(sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_437]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_440,plain,
% 3.00/0.92      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_438,c_26,c_25]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_19,plain,
% 3.00/0.92      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | v2_struct_0(X1)
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 3.00/0.92      inference(cnf_transformation,[],[f70]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_800,plain,
% 3.00/0.92      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.92      | ~ v2_pre_topc(X1)
% 3.00/0.92      | ~ l1_pre_topc(X1)
% 3.00/0.92      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 3.00/0.92      | sK0 != X1 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_801,plain,
% 3.00/0.92      ( r2_hidden(X0,u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | ~ v2_pre_topc(sK0)
% 3.00/0.92      | ~ l1_pre_topc(sK0)
% 3.00/0.92      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_800]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_805,plain,
% 3.00/0.92      ( r2_hidden(X0,u1_pre_topc(sK0))
% 3.00/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_801,c_27,c_26]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_1044,plain,
% 3.00/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 3.00/0.92      | u1_pre_topc(sK0) != u1_pre_topc(sK0)
% 3.00/0.92      | sK1 != X0 ),
% 3.00/0.92      inference(resolution_lifted,[status(thm)],[c_440,c_805]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_1045,plain,
% 3.00/0.92      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.00/0.92      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(unflattening,[status(thm)],[c_1044]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(c_1047,plain,
% 3.00/0.92      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 3.00/0.92      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 3.00/0.92      inference(global_propositional_subsumption,
% 3.00/0.92                [status(thm)],
% 3.00/0.92                [c_1045,c_25]) ).
% 3.00/0.92  
% 3.00/0.92  cnf(contradiction,plain,
% 3.00/0.92      ( $false ),
% 3.00/0.92      inference(minisat,[status(thm)],[c_5407,c_5341,c_1047]) ).
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/0.92  
% 3.00/0.92  ------                               Statistics
% 3.00/0.92  
% 3.00/0.92  ------ General
% 3.00/0.92  
% 3.00/0.92  abstr_ref_over_cycles:                  0
% 3.00/0.92  abstr_ref_under_cycles:                 0
% 3.00/0.92  gc_basic_clause_elim:                   0
% 3.00/0.92  forced_gc_time:                         0
% 3.00/0.92  parsing_time:                           0.008
% 3.00/0.92  unif_index_cands_time:                  0.
% 3.00/0.92  unif_index_add_time:                    0.
% 3.00/0.92  orderings_time:                         0.
% 3.00/0.92  out_proof_time:                         0.012
% 3.00/0.92  total_time:                             0.168
% 3.00/0.92  num_of_symbols:                         52
% 3.00/0.92  num_of_terms:                           4038
% 3.00/0.92  
% 3.00/0.92  ------ Preprocessing
% 3.00/0.92  
% 3.00/0.92  num_of_splits:                          0
% 3.00/0.92  num_of_split_atoms:                     0
% 3.00/0.92  num_of_reused_defs:                     0
% 3.00/0.92  num_eq_ax_congr_red:                    14
% 3.00/0.92  num_of_sem_filtered_clauses:            1
% 3.00/0.92  num_of_subtypes:                        0
% 3.00/0.92  monotx_restored_types:                  0
% 3.00/0.92  sat_num_of_epr_types:                   0
% 3.00/0.92  sat_num_of_non_cyclic_types:            0
% 3.00/0.92  sat_guarded_non_collapsed_types:        0
% 3.00/0.92  num_pure_diseq_elim:                    0
% 3.00/0.92  simp_replaced_by:                       0
% 3.00/0.92  res_preprocessed:                       120
% 3.00/0.92  prep_upred:                             0
% 3.00/0.92  prep_unflattend:                        46
% 3.00/0.92  smt_new_axioms:                         0
% 3.00/0.92  pred_elim_cands:                        4
% 3.00/0.92  pred_elim:                              6
% 3.00/0.92  pred_elim_cl:                           7
% 3.00/0.92  pred_elim_cycles:                       12
% 3.00/0.92  merged_defs:                            8
% 3.00/0.92  merged_defs_ncl:                        0
% 3.00/0.92  bin_hyper_res:                          9
% 3.00/0.92  prep_cycles:                            4
% 3.00/0.92  pred_elim_time:                         0.016
% 3.00/0.92  splitting_time:                         0.
% 3.00/0.92  sem_filter_time:                        0.
% 3.00/0.92  monotx_time:                            0.001
% 3.00/0.92  subtype_inf_time:                       0.
% 3.00/0.92  
% 3.00/0.92  ------ Problem properties
% 3.00/0.92  
% 3.00/0.92  clauses:                                21
% 3.00/0.92  conjectures:                            2
% 3.00/0.92  epr:                                    3
% 3.00/0.92  horn:                                   20
% 3.00/0.92  ground:                                 4
% 3.00/0.92  unary:                                  5
% 3.00/0.92  binary:                                 9
% 3.00/0.92  lits:                                   45
% 3.00/0.92  lits_eq:                                11
% 3.00/0.92  fd_pure:                                0
% 3.00/0.92  fd_pseudo:                              0
% 3.00/0.92  fd_cond:                                0
% 3.00/0.92  fd_pseudo_cond:                         1
% 3.00/0.92  ac_symbols:                             0
% 3.00/0.92  
% 3.00/0.92  ------ Propositional Solver
% 3.00/0.92  
% 3.00/0.92  prop_solver_calls:                      28
% 3.00/0.92  prop_fast_solver_calls:                 1036
% 3.00/0.92  smt_solver_calls:                       0
% 3.00/0.92  smt_fast_solver_calls:                  0
% 3.00/0.92  prop_num_of_clauses:                    1780
% 3.00/0.92  prop_preprocess_simplified:             5556
% 3.00/0.92  prop_fo_subsumed:                       49
% 3.00/0.92  prop_solver_time:                       0.
% 3.00/0.92  smt_solver_time:                        0.
% 3.00/0.92  smt_fast_solver_time:                   0.
% 3.00/0.92  prop_fast_solver_time:                  0.
% 3.00/0.92  prop_unsat_core_time:                   0.
% 3.00/0.92  
% 3.00/0.92  ------ QBF
% 3.00/0.92  
% 3.00/0.92  qbf_q_res:                              0
% 3.00/0.92  qbf_num_tautologies:                    0
% 3.00/0.92  qbf_prep_cycles:                        0
% 3.00/0.92  
% 3.00/0.92  ------ BMC1
% 3.00/0.92  
% 3.00/0.92  bmc1_current_bound:                     -1
% 3.00/0.92  bmc1_last_solved_bound:                 -1
% 3.00/0.92  bmc1_unsat_core_size:                   -1
% 3.00/0.92  bmc1_unsat_core_parents_size:           -1
% 3.00/0.92  bmc1_merge_next_fun:                    0
% 3.00/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.00/0.92  
% 3.00/0.92  ------ Instantiation
% 3.00/0.92  
% 3.00/0.92  inst_num_of_clauses:                    593
% 3.00/0.92  inst_num_in_passive:                    236
% 3.00/0.92  inst_num_in_active:                     331
% 3.00/0.92  inst_num_in_unprocessed:                26
% 3.00/0.92  inst_num_of_loops:                      340
% 3.00/0.92  inst_num_of_learning_restarts:          0
% 3.00/0.92  inst_num_moves_active_passive:          5
% 3.00/0.92  inst_lit_activity:                      0
% 3.00/0.92  inst_lit_activity_moves:                0
% 3.00/0.92  inst_num_tautologies:                   0
% 3.00/0.92  inst_num_prop_implied:                  0
% 3.00/0.92  inst_num_existing_simplified:           0
% 3.00/0.92  inst_num_eq_res_simplified:             0
% 3.00/0.92  inst_num_child_elim:                    0
% 3.00/0.92  inst_num_of_dismatching_blockings:      218
% 3.00/0.92  inst_num_of_non_proper_insts:           648
% 3.00/0.92  inst_num_of_duplicates:                 0
% 3.00/0.92  inst_inst_num_from_inst_to_res:         0
% 3.00/0.92  inst_dismatching_checking_time:         0.
% 3.00/0.92  
% 3.00/0.92  ------ Resolution
% 3.00/0.92  
% 3.00/0.92  res_num_of_clauses:                     0
% 3.00/0.92  res_num_in_passive:                     0
% 3.00/0.92  res_num_in_active:                      0
% 3.00/0.92  res_num_of_loops:                       124
% 3.00/0.92  res_forward_subset_subsumed:            42
% 3.00/0.92  res_backward_subset_subsumed:           0
% 3.00/0.92  res_forward_subsumed:                   2
% 3.00/0.92  res_backward_subsumed:                  0
% 3.00/0.92  res_forward_subsumption_resolution:     0
% 3.00/0.92  res_backward_subsumption_resolution:    0
% 3.00/0.92  res_clause_to_clause_subsumption:       231
% 3.00/0.92  res_orphan_elimination:                 0
% 3.00/0.92  res_tautology_del:                      86
% 3.00/0.92  res_num_eq_res_simplified:              0
% 3.00/0.92  res_num_sel_changes:                    0
% 3.00/0.92  res_moves_from_active_to_pass:          0
% 3.00/0.92  
% 3.00/0.92  ------ Superposition
% 3.00/0.92  
% 3.00/0.92  sup_time_total:                         0.
% 3.00/0.92  sup_time_generating:                    0.
% 3.00/0.92  sup_time_sim_full:                      0.
% 3.00/0.92  sup_time_sim_immed:                     0.
% 3.00/0.92  
% 3.00/0.92  sup_num_of_clauses:                     54
% 3.00/0.92  sup_num_in_active:                      45
% 3.00/0.92  sup_num_in_passive:                     9
% 3.00/0.92  sup_num_of_loops:                       66
% 3.00/0.92  sup_fw_superposition:                   35
% 3.00/0.92  sup_bw_superposition:                   36
% 3.00/0.92  sup_immediate_simplified:               26
% 3.00/0.92  sup_given_eliminated:                   0
% 3.00/0.92  comparisons_done:                       0
% 3.00/0.92  comparisons_avoided:                    6
% 3.00/0.92  
% 3.00/0.92  ------ Simplifications
% 3.00/0.92  
% 3.00/0.92  
% 3.00/0.92  sim_fw_subset_subsumed:                 7
% 3.00/0.92  sim_bw_subset_subsumed:                 8
% 3.00/0.92  sim_fw_subsumed:                        4
% 3.00/0.92  sim_bw_subsumed:                        0
% 3.00/0.92  sim_fw_subsumption_res:                 3
% 3.00/0.92  sim_bw_subsumption_res:                 0
% 3.00/0.92  sim_tautology_del:                      0
% 3.00/0.92  sim_eq_tautology_del:                   3
% 3.00/0.92  sim_eq_res_simp:                        0
% 3.00/0.92  sim_fw_demodulated:                     2
% 3.00/0.92  sim_bw_demodulated:                     18
% 3.00/0.92  sim_light_normalised:                   19
% 3.00/0.92  sim_joinable_taut:                      0
% 3.00/0.92  sim_joinable_simp:                      0
% 3.00/0.92  sim_ac_normalised:                      0
% 3.00/0.92  sim_smt_subsumption:                    0
% 3.00/0.92  
%------------------------------------------------------------------------------
