%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:33 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 597 expanded)
%              Number of clauses        :  143 ( 246 expanded)
%              Number of leaves         :   21 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          :  684 (2364 expanded)
%              Number of equality atoms :  231 ( 565 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v3_tdlat_3(sK2)
        & v3_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tdlat_3(X1)
            & v3_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(sK1)
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ v3_tdlat_3(sK2)
    & v3_tdlat_3(sK1)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f40,f39])).

fof(f63,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
        & r2_hidden(sK0(X0),u1_pre_topc(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
            & r2_hidden(sK0(X0),u1_pre_topc(X0))
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f57,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | r2_hidden(sK0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27725,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_178,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_4])).

cnf(c_179,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_27716,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_179])).

cnf(c_21,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27730,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_28796,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_27730])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25180,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_26038,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_25180])).

cnf(c_28917,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28796,c_24,c_26038])).

cnf(c_28918,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_28917])).

cnf(c_28923,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27716,c_28918])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25168,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_179])).

cnf(c_26171,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26038,c_24])).

cnf(c_26172,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_26171])).

cnf(c_26177,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25168,c_26172])).

cnf(c_29055,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28923,c_25,c_26177])).

cnf(c_29056,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_29055])).

cnf(c_29061,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27725,c_29056])).

cnf(c_29318,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29061,c_25])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27724,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27735,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_28351,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27724,c_27735])).

cnf(c_30154,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_27724,c_28351])).

cnf(c_58,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12946,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12956,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13694,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12946,c_12956])).

cnf(c_14294,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12946,c_13694])).

cnf(c_30366,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30154,c_58,c_14294])).

cnf(c_30367,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_30366])).

cnf(c_30377,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29318,c_30367])).

cnf(c_29062,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29061])).

cnf(c_25827,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_25168])).

cnf(c_25917,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25827,c_24])).

cnf(c_25918,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_25917])).

cnf(c_26037,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25918,c_25180])).

cnf(c_26058,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26037])).

cnf(c_26060,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_26058])).

cnf(c_26059,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_26037])).

cnf(c_314,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_20443,plain,
    ( X0 != u1_struct_0(X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_20481,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_20443])).

cnf(c_24981,plain,
    ( u1_struct_0(sK2) != u1_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_20481])).

cnf(c_24982,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_24981])).

cnf(c_20395,plain,
    ( X0 != k1_zfmisc_1(u1_struct_0(X1))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_20406,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(X1))
    | k1_zfmisc_1(k1_zfmisc_1(X0)) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_20395])).

cnf(c_20485,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(X1))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_20406])).

cnf(c_24867,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X0))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_20485])).

cnf(c_24868,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_24867])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_20346,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | X0 != u1_pre_topc(X2)
    | X1 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_20852,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | X0 != u1_pre_topc(X2)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(instantiation,[status(thm)],[c_20346])).

cnf(c_22985,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | u1_pre_topc(X0) != u1_pre_topc(X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_20852])).

cnf(c_22986,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_22985])).

cnf(c_24391,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_22986])).

cnf(c_24393,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_24391])).

cnf(c_12,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24378,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18624,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_18764,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),sK2)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_18624])).

cnf(c_18766,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | v1_tops_2(u1_pre_topc(sK1),sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18764])).

cnf(c_11,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18636,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18747,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),sK2)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18636])).

cnf(c_18749,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK2)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18747])).

cnf(c_311,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_13374,plain,
    ( X0 != X1
    | X0 = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) != X1 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_13918,plain,
    ( X0 != k1_zfmisc_1(X1)
    | X0 = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_13374])).

cnf(c_13991,plain,
    ( X0 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))
    | X0 = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_13918])).

cnf(c_14134,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_13991])).

cnf(c_14135,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_14134])).

cnf(c_18247,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_14135])).

cnf(c_18248,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_18247])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17943,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13339,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | X0 != u1_pre_topc(X2)
    | X1 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_13898,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | X0 != u1_pre_topc(X2)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(instantiation,[status(thm)],[c_13339])).

cnf(c_16147,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | u1_pre_topc(X0) != u1_pre_topc(X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_13898])).

cnf(c_16148,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_16147])).

cnf(c_17519,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_16148])).

cnf(c_17521,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_17519])).

cnf(c_13195,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_17213,plain,
    ( v1_tops_2(u1_pre_topc(sK2),X0)
    | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13195])).

cnf(c_17215,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK1)
    | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17213])).

cnf(c_13210,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_14930,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK2),X0)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_13210])).

cnf(c_14932,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK2),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14930])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7198,plain,
    ( ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | m1_subset_1(sK0(sK2),X0)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7343,plain,
    ( ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ),
    inference(instantiation,[status(thm)],[c_7198])).

cnf(c_7345,plain,
    ( ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_7343])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7330,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_7332,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_7330])).

cnf(c_15,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6476,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_323,plain,
    ( X0 != X1
    | X2 != X3
    | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_5929,plain,
    ( X0 != sK0(sK2)
    | X1 != u1_struct_0(X2)
    | k6_subset_1(X1,X0) = k6_subset_1(u1_struct_0(X2),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_5965,plain,
    ( X0 != u1_struct_0(X1)
    | k6_subset_1(X0,sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
    | sK0(sK2) != sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_5929])).

cnf(c_5966,plain,
    ( X0 != u1_struct_0(X1)
    | k6_subset_1(X0,sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_5965])).

cnf(c_6082,plain,
    ( k6_subset_1(u1_struct_0(X0),sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
    | u1_struct_0(X0) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_5966])).

cnf(c_6439,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6082])).

cnf(c_6440,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6439])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5730,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
    | X0 != k6_subset_1(u1_struct_0(X2),sK0(sK2))
    | X1 != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_5917,plain,
    ( r2_hidden(k6_subset_1(X0,X1),X2)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X3),sK0(sK2)),u1_pre_topc(X3))
    | X2 != u1_pre_topc(X3)
    | k6_subset_1(X0,X1) != k6_subset_1(u1_struct_0(X3),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5730])).

cnf(c_6085,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
    | X1 != u1_pre_topc(X2)
    | k6_subset_1(u1_struct_0(X0),sK0(sK2)) != k6_subset_1(u1_struct_0(X2),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5917])).

cnf(c_6125,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),sK0(sK2)),u1_pre_topc(X2))
    | k6_subset_1(u1_struct_0(X1),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_pre_topc(X2) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6085])).

cnf(c_6350,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_pre_topc(sK2) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6125])).

cnf(c_6352,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6350])).

cnf(c_5052,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ r1_tarski(u1_pre_topc(X1),X0)
    | X0 = u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5198,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_5052])).

cnf(c_5379,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
    | u1_pre_topc(sK2) = u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_5198])).

cnf(c_5381,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    | u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5379])).

cnf(c_5372,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
    | u1_pre_topc(X0) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5198])).

cnf(c_5374,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    | u1_pre_topc(sK1) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5372])).

cnf(c_4986,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | X0 != sK0(sK2)
    | X1 != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_5008,plain,
    ( r2_hidden(sK0(sK2),X0)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | X0 != u1_pre_topc(sK2)
    | sK0(sK2) != sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_4986])).

cnf(c_5009,plain,
    ( r2_hidden(sK0(sK2),X0)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | X0 != u1_pre_topc(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_5008])).

cnf(c_5076,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | u1_pre_topc(X0) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5009])).

cnf(c_5078,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | u1_pre_topc(sK1) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5076])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4025,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_56,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_41,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_39,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_38,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_19,negated_conjecture,
    ( ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30377,c_29062,c_26060,c_26059,c_24982,c_24868,c_24393,c_24378,c_18766,c_18749,c_18248,c_17943,c_17521,c_17215,c_14932,c_7345,c_7332,c_6476,c_6440,c_6352,c_5381,c_5374,c_5078,c_4025,c_56,c_41,c_39,c_38,c_19,c_20,c_25,c_22,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.35  % Computer   : n002.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.39/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/1.52  
% 7.39/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.39/1.52  
% 7.39/1.52  ------  iProver source info
% 7.39/1.52  
% 7.39/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.39/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.39/1.52  git: non_committed_changes: false
% 7.39/1.52  git: last_make_outside_of_git: false
% 7.39/1.52  
% 7.39/1.52  ------ 
% 7.39/1.52  ------ Parsing...
% 7.39/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  ------ Proving...
% 7.39/1.52  ------ Problem Properties 
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  clauses                                 22
% 7.39/1.52  conjectures                             5
% 7.39/1.52  EPR                                     8
% 7.39/1.52  Horn                                    20
% 7.39/1.52  unary                                   6
% 7.39/1.52  binary                                  3
% 7.39/1.52  lits                                    58
% 7.39/1.52  lits eq                                 2
% 7.39/1.52  fd_pure                                 0
% 7.39/1.52  fd_pseudo                               0
% 7.39/1.52  fd_cond                                 0
% 7.39/1.52  fd_pseudo_cond                          1
% 7.39/1.52  AC symbols                              0
% 7.39/1.52  
% 7.39/1.52  ------ Input Options Time Limit: Unbounded
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing...
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.39/1.52  Current options:
% 7.39/1.52  ------ 
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.39/1.52  
% 7.39/1.52  ------ Proving...
% 7.39/1.52  
% 7.39/1.52  
% 7.39/1.52  % SZS status Theorem for theBenchmark.p
% 7.39/1.52  
% 7.39/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.39/1.52  
% 7.39/1.52  fof(f10,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f25,plain,(
% 7.39/1.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f10])).
% 7.39/1.52  
% 7.39/1.52  fof(f55,plain,(
% 7.39/1.52    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f25])).
% 7.39/1.52  
% 7.39/1.52  fof(f6,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f20,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f6])).
% 7.39/1.52  
% 7.39/1.52  fof(f33,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(nnf_transformation,[],[f20])).
% 7.39/1.52  
% 7.39/1.52  fof(f49,plain,(
% 7.39/1.52    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f33])).
% 7.39/1.52  
% 7.39/1.52  fof(f3,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f17,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f3])).
% 7.39/1.52  
% 7.39/1.52  fof(f46,plain,(
% 7.39/1.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f17])).
% 7.39/1.52  
% 7.39/1.52  fof(f13,conjecture,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f14,negated_conjecture,(
% 7.39/1.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 7.39/1.52    inference(negated_conjecture,[],[f13])).
% 7.39/1.52  
% 7.39/1.52  fof(f29,plain,(
% 7.39/1.52    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f14])).
% 7.39/1.52  
% 7.39/1.52  fof(f30,plain,(
% 7.39/1.52    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 7.39/1.52    inference(flattening,[],[f29])).
% 7.39/1.52  
% 7.39/1.52  fof(f40,plain,(
% 7.39/1.52    ( ! [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK2) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK2))) )),
% 7.39/1.52    introduced(choice_axiom,[])).
% 7.39/1.52  
% 7.39/1.52  fof(f39,plain,(
% 7.39/1.52    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK1))),
% 7.39/1.52    introduced(choice_axiom,[])).
% 7.39/1.52  
% 7.39/1.52  fof(f41,plain,(
% 7.39/1.52    (~v3_tdlat_3(sK2) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2)) & l1_pre_topc(sK1)),
% 7.39/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f40,f39])).
% 7.39/1.52  
% 7.39/1.52  fof(f63,plain,(
% 7.39/1.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 7.39/1.52    inference(cnf_transformation,[],[f41])).
% 7.39/1.52  
% 7.39/1.52  fof(f5,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f19,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f5])).
% 7.39/1.52  
% 7.39/1.52  fof(f48,plain,(
% 7.39/1.52    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f19])).
% 7.39/1.52  
% 7.39/1.52  fof(f61,plain,(
% 7.39/1.52    l1_pre_topc(sK1)),
% 7.39/1.52    inference(cnf_transformation,[],[f41])).
% 7.39/1.52  
% 7.39/1.52  fof(f62,plain,(
% 7.39/1.52    l1_pre_topc(sK2)),
% 7.39/1.52    inference(cnf_transformation,[],[f41])).
% 7.39/1.52  
% 7.39/1.52  fof(f11,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f26,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f11])).
% 7.39/1.52  
% 7.39/1.52  fof(f56,plain,(
% 7.39/1.52    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f26])).
% 7.39/1.52  
% 7.39/1.52  fof(f1,axiom,(
% 7.39/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f31,plain,(
% 7.39/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.39/1.52    inference(nnf_transformation,[],[f1])).
% 7.39/1.52  
% 7.39/1.52  fof(f32,plain,(
% 7.39/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.39/1.52    inference(flattening,[],[f31])).
% 7.39/1.52  
% 7.39/1.52  fof(f44,plain,(
% 7.39/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f32])).
% 7.39/1.52  
% 7.39/1.52  fof(f9,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f24,plain,(
% 7.39/1.52    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f9])).
% 7.39/1.52  
% 7.39/1.52  fof(f54,plain,(
% 7.39/1.52    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f24])).
% 7.39/1.52  
% 7.39/1.52  fof(f7,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f21,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f7])).
% 7.39/1.52  
% 7.39/1.52  fof(f22,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(flattening,[],[f21])).
% 7.39/1.52  
% 7.39/1.52  fof(f51,plain,(
% 7.39/1.52    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f22])).
% 7.39/1.52  
% 7.39/1.52  fof(f68,plain,(
% 7.39/1.52    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(equality_resolution,[],[f51])).
% 7.39/1.52  
% 7.39/1.52  fof(f8,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f23,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f8])).
% 7.39/1.52  
% 7.39/1.52  fof(f34,plain,(
% 7.39/1.52    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(nnf_transformation,[],[f23])).
% 7.39/1.52  
% 7.39/1.52  fof(f52,plain,(
% 7.39/1.52    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f34])).
% 7.39/1.52  
% 7.39/1.52  fof(f4,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f18,plain,(
% 7.39/1.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f4])).
% 7.39/1.52  
% 7.39/1.52  fof(f47,plain,(
% 7.39/1.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f18])).
% 7.39/1.52  
% 7.39/1.52  fof(f2,axiom,(
% 7.39/1.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f15,plain,(
% 7.39/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.39/1.52    inference(ennf_transformation,[],[f2])).
% 7.39/1.52  
% 7.39/1.52  fof(f16,plain,(
% 7.39/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.39/1.52    inference(flattening,[],[f15])).
% 7.39/1.52  
% 7.39/1.52  fof(f45,plain,(
% 7.39/1.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f16])).
% 7.39/1.52  
% 7.39/1.52  fof(f12,axiom,(
% 7.39/1.52    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 7.39/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.52  
% 7.39/1.52  fof(f27,plain,(
% 7.39/1.52    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(ennf_transformation,[],[f12])).
% 7.39/1.52  
% 7.39/1.52  fof(f28,plain,(
% 7.39/1.52    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(flattening,[],[f27])).
% 7.39/1.52  
% 7.39/1.52  fof(f35,plain,(
% 7.39/1.52    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(nnf_transformation,[],[f28])).
% 7.39/1.52  
% 7.39/1.52  fof(f36,plain,(
% 7.39/1.52    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(rectify,[],[f35])).
% 7.39/1.52  
% 7.39/1.52  fof(f37,plain,(
% 7.39/1.52    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.39/1.52    introduced(choice_axiom,[])).
% 7.39/1.52  
% 7.39/1.52  fof(f38,plain,(
% 7.39/1.52    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.39/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 7.39/1.52  
% 7.39/1.52  fof(f57,plain,(
% 7.39/1.52    ( ! [X2,X0] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f38])).
% 7.39/1.52  
% 7.39/1.52  fof(f60,plain,(
% 7.39/1.52    ( ! [X0] : (v3_tdlat_3(X0) | ~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f38])).
% 7.39/1.52  
% 7.39/1.52  fof(f59,plain,(
% 7.39/1.52    ( ! [X0] : (v3_tdlat_3(X0) | r2_hidden(sK0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 7.39/1.52    inference(cnf_transformation,[],[f38])).
% 7.39/1.52  
% 7.39/1.52  fof(f65,plain,(
% 7.39/1.52    ~v3_tdlat_3(sK2)),
% 7.39/1.52    inference(cnf_transformation,[],[f41])).
% 7.39/1.52  
% 7.39/1.52  fof(f64,plain,(
% 7.39/1.52    v3_tdlat_3(sK1)),
% 7.39/1.52    inference(cnf_transformation,[],[f41])).
% 7.39/1.52  
% 7.39/1.52  cnf(c_13,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.39/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_27725,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X0) = iProver_top
% 7.39/1.52      | l1_pre_topc(X0) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_8,plain,
% 7.39/1.52      ( ~ m1_pre_topc(X0,X1)
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.39/1.52      | ~ l1_pre_topc(X0)
% 7.39/1.52      | ~ l1_pre_topc(X1) ),
% 7.39/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_4,plain,
% 7.39/1.52      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.39/1.52      inference(cnf_transformation,[],[f46]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_178,plain,
% 7.39/1.52      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.39/1.52      | ~ m1_pre_topc(X0,X1)
% 7.39/1.52      | ~ l1_pre_topc(X1) ),
% 7.39/1.52      inference(global_propositional_subsumption,[status(thm)],[c_8,c_4]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_179,plain,
% 7.39/1.52      ( ~ m1_pre_topc(X0,X1)
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.39/1.52      | ~ l1_pre_topc(X1) ),
% 7.39/1.52      inference(renaming,[status(thm)],[c_178]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_27716,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_179]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_21,negated_conjecture,
% 7.39/1.52      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.39/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_6,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1)
% 7.39/1.52      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.39/1.52      | ~ l1_pre_topc(X1) ),
% 7.39/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_27730,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_28796,plain,
% 7.39/1.52      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK1) = iProver_top
% 7.39/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_21,c_27730]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_23,negated_conjecture,
% 7.39/1.52      ( l1_pre_topc(sK1) ),
% 7.39/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_24,plain,
% 7.39/1.52      ( l1_pre_topc(sK1) = iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_25180,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26038,plain,
% 7.39/1.52      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK1) = iProver_top
% 7.39/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_21,c_25180]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_28917,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.39/1.52      inference(global_propositional_subsumption,
% 7.39/1.52                [status(thm)],
% 7.39/1.52                [c_28796,c_24,c_26038]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_28918,plain,
% 7.39/1.52      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK1) = iProver_top ),
% 7.39/1.52      inference(renaming,[status(thm)],[c_28917]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_28923,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.39/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_27716,c_28918]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_22,negated_conjecture,
% 7.39/1.52      ( l1_pre_topc(sK2) ),
% 7.39/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_25,plain,
% 7.39/1.52      ( l1_pre_topc(sK2) = iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_25168,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_179]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26171,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.39/1.52      inference(global_propositional_subsumption,
% 7.39/1.52                [status(thm)],
% 7.39/1.52                [c_26038,c_24]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26172,plain,
% 7.39/1.52      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK1) = iProver_top ),
% 7.39/1.52      inference(renaming,[status(thm)],[c_26171]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26177,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK2) != iProver_top
% 7.39/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_25168,c_26172]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_29055,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK1) = iProver_top ),
% 7.39/1.52      inference(global_propositional_subsumption,
% 7.39/1.52                [status(thm)],
% 7.39/1.52                [c_28923,c_25,c_26177]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_29056,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.39/1.52      inference(renaming,[status(thm)],[c_29055]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_29061,plain,
% 7.39/1.52      ( m1_pre_topc(sK2,sK1) = iProver_top
% 7.39/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_27725,c_29056]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_29318,plain,
% 7.39/1.52      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.39/1.52      inference(global_propositional_subsumption,
% 7.39/1.52                [status(thm)],
% 7.39/1.52                [c_29061,c_25]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_14,plain,
% 7.39/1.52      ( ~ m1_pre_topc(X0,X1)
% 7.39/1.52      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.39/1.52      | ~ l1_pre_topc(X1) ),
% 7.39/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_27724,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_0,plain,
% 7.39/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.39/1.52      inference(cnf_transformation,[],[f44]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_27735,plain,
% 7.39/1.52      ( X0 = X1
% 7.39/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.39/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_28351,plain,
% 7.39/1.52      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.39/1.52      | m1_pre_topc(X1,X0) != iProver_top
% 7.39/1.52      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.39/1.52      | l1_pre_topc(X0) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_27724,c_27735]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_30154,plain,
% 7.39/1.52      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.39/1.52      | m1_pre_topc(X1,X0) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | l1_pre_topc(X0) != iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_27724,c_28351]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_58,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top
% 7.39/1.52      | l1_pre_topc(X0) = iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_12946,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_12956,plain,
% 7.39/1.52      ( X0 = X1
% 7.39/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.39/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.39/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_13694,plain,
% 7.39/1.52      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.39/1.52      | m1_pre_topc(X1,X0) != iProver_top
% 7.39/1.52      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.39/1.52      | l1_pre_topc(X0) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_12946,c_12956]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_14294,plain,
% 7.39/1.52      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.39/1.52      | m1_pre_topc(X1,X0) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | l1_pre_topc(X0) != iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_12946,c_13694]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_30366,plain,
% 7.39/1.52      ( m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | m1_pre_topc(X1,X0) != iProver_top
% 7.39/1.52      | u1_struct_0(X0) = u1_struct_0(X1)
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(global_propositional_subsumption,
% 7.39/1.52                [status(thm)],
% 7.39/1.52                [c_30154,c_58,c_14294]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_30367,plain,
% 7.39/1.52      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.39/1.52      | m1_pre_topc(X0,X1) != iProver_top
% 7.39/1.52      | m1_pre_topc(X1,X0) != iProver_top
% 7.39/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.39/1.52      inference(renaming,[status(thm)],[c_30366]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_30377,plain,
% 7.39/1.52      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 7.39/1.52      | m1_pre_topc(sK1,sK2) != iProver_top
% 7.39/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_29318,c_30367]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_29062,plain,
% 7.39/1.52      ( m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK2) ),
% 7.39/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_29061]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_25827,plain,
% 7.39/1.52      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK1) != iProver_top
% 7.39/1.52      | l1_pre_topc(sK1) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_21,c_25168]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_25917,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.39/1.52      inference(global_propositional_subsumption,
% 7.39/1.52                [status(thm)],
% 7.39/1.52                [c_25827,c_24]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_25918,plain,
% 7.39/1.52      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK1) != iProver_top ),
% 7.39/1.52      inference(renaming,[status(thm)],[c_25917]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26037,plain,
% 7.39/1.52      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.39/1.52      | m1_pre_topc(X0,sK2) = iProver_top
% 7.39/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.39/1.52      inference(superposition,[status(thm)],[c_25918,c_25180]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26058,plain,
% 7.39/1.52      ( ~ m1_pre_topc(X0,sK1)
% 7.39/1.52      | m1_pre_topc(X0,sK2)
% 7.39/1.52      | ~ l1_pre_topc(sK2) ),
% 7.39/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_26037]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26060,plain,
% 7.39/1.52      ( ~ m1_pre_topc(sK1,sK1)
% 7.39/1.52      | m1_pre_topc(sK1,sK2)
% 7.39/1.52      | ~ l1_pre_topc(sK2) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_26058]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_26059,plain,
% 7.39/1.52      ( m1_pre_topc(sK1,sK1) != iProver_top
% 7.39/1.52      | m1_pre_topc(sK1,sK2) = iProver_top
% 7.39/1.52      | l1_pre_topc(sK2) != iProver_top ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_26037]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_314,plain,
% 7.39/1.52      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.39/1.52      theory(equality) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_20443,plain,
% 7.39/1.52      ( X0 != u1_struct_0(X1)
% 7.39/1.52      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_314]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_20481,plain,
% 7.39/1.52      ( u1_struct_0(X0) != u1_struct_0(X1)
% 7.39/1.52      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_20443]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_24981,plain,
% 7.39/1.52      ( u1_struct_0(sK2) != u1_struct_0(X0)
% 7.39/1.52      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_20481]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_24982,plain,
% 7.39/1.52      ( u1_struct_0(sK2) != u1_struct_0(sK1)
% 7.39/1.52      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_24981]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_20395,plain,
% 7.39/1.52      ( X0 != k1_zfmisc_1(u1_struct_0(X1))
% 7.39/1.52      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_314]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_20406,plain,
% 7.39/1.52      ( k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(X1))
% 7.39/1.52      | k1_zfmisc_1(k1_zfmisc_1(X0)) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_20395]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_20485,plain,
% 7.39/1.52      ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(X1))
% 7.39/1.52      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_20406]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_24867,plain,
% 7.39/1.52      ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X0))
% 7.39/1.52      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.52      inference(instantiation,[status(thm)],[c_20485]) ).
% 7.39/1.52  
% 7.39/1.52  cnf(c_24868,plain,
% 7.39/1.52      ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_24867]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_313,plain,
% 7.39/1.53      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.39/1.53      theory(equality) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_20346,plain,
% 7.39/1.53      ( m1_subset_1(X0,X1)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 7.39/1.53      | X0 != u1_pre_topc(X2)
% 7.39/1.53      | X1 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_313]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_20852,plain,
% 7.39/1.53      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 7.39/1.53      | X0 != u1_pre_topc(X2)
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_20346]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_22985,plain,
% 7.39/1.53      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | u1_pre_topc(X0) != u1_pre_topc(X0)
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_20852]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_22986,plain,
% 7.39/1.53      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.53      inference(equality_resolution_simp,[status(thm)],[c_22985]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_24391,plain,
% 7.39/1.53      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_22986]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_24393,plain,
% 7.39/1.53      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.39/1.53      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_24391]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_12,plain,
% 7.39/1.53      ( v1_tops_2(u1_pre_topc(X0),X0) | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(cnf_transformation,[],[f54]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_24378,plain,
% 7.39/1.53      ( v1_tops_2(u1_pre_topc(sK2),sK2) | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_12]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_9,plain,
% 7.39/1.53      ( ~ v1_tops_2(X0,X1)
% 7.39/1.53      | v1_tops_2(X0,X2)
% 7.39/1.53      | ~ m1_pre_topc(X2,X1)
% 7.39/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 7.39/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | ~ l1_pre_topc(X1) ),
% 7.39/1.53      inference(cnf_transformation,[],[f68]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18624,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 7.39/1.53      | v1_tops_2(u1_pre_topc(X0),X1)
% 7.39/1.53      | ~ m1_pre_topc(X1,X0)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18764,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 7.39/1.53      | v1_tops_2(u1_pre_topc(X0),sK2)
% 7.39/1.53      | ~ m1_pre_topc(sK2,X0)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_18624]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18766,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(sK1),sK1)
% 7.39/1.53      | v1_tops_2(u1_pre_topc(sK1),sK2)
% 7.39/1.53      | ~ m1_pre_topc(sK2,sK1)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | ~ l1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_18764]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_11,plain,
% 7.39/1.53      ( ~ v1_tops_2(X0,X1)
% 7.39/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | r1_tarski(X0,u1_pre_topc(X1))
% 7.39/1.53      | ~ l1_pre_topc(X1) ),
% 7.39/1.53      inference(cnf_transformation,[],[f52]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18636,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(X0),X1)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 7.39/1.53      | ~ l1_pre_topc(X1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_11]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18747,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(X0),sK2)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 7.39/1.53      | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_18636]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18749,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(sK1),sK2)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
% 7.39/1.53      | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_18747]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_311,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_13374,plain,
% 7.39/1.53      ( X0 != X1
% 7.39/1.53      | X0 = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) != X1 ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_311]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_13918,plain,
% 7.39/1.53      ( X0 != k1_zfmisc_1(X1)
% 7.39/1.53      | X0 = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) != k1_zfmisc_1(X1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13374]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_13991,plain,
% 7.39/1.53      ( X0 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))
% 7.39/1.53      | X0 = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13918]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_14134,plain,
% 7.39/1.53      ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13991]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_14135,plain,
% 7.39/1.53      ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.53      inference(equality_resolution_simp,[status(thm)],[c_14134]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18247,plain,
% 7.39/1.53      ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_14135]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18248,plain,
% 7.39/1.53      ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) = k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_18247]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5,plain,
% 7.39/1.53      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(cnf_transformation,[],[f47]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_17943,plain,
% 7.39/1.53      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_13339,plain,
% 7.39/1.53      ( m1_subset_1(X0,X1)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 7.39/1.53      | X0 != u1_pre_topc(X2)
% 7.39/1.53      | X1 != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_313]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_13898,plain,
% 7.39/1.53      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 7.39/1.53      | X0 != u1_pre_topc(X2)
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13339]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_16147,plain,
% 7.39/1.53      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | u1_pre_topc(X0) != u1_pre_topc(X0)
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13898]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_16148,plain,
% 7.39/1.53      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.39/1.53      inference(equality_resolution_simp,[status(thm)],[c_16147]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_17519,plain,
% 7.39/1.53      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_16148]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_17521,plain,
% 7.39/1.53      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) != k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_17519]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_13195,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 7.39/1.53      | v1_tops_2(u1_pre_topc(X0),X1)
% 7.39/1.53      | ~ m1_pre_topc(X1,X0)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_17213,plain,
% 7.39/1.53      ( v1_tops_2(u1_pre_topc(sK2),X0)
% 7.39/1.53      | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
% 7.39/1.53      | ~ m1_pre_topc(X0,sK2)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13195]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_17215,plain,
% 7.39/1.53      ( v1_tops_2(u1_pre_topc(sK2),sK1)
% 7.39/1.53      | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
% 7.39/1.53      | ~ m1_pre_topc(sK1,sK2)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.39/1.53      | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_17213]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_13210,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(X0),X1)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.39/1.53      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 7.39/1.53      | ~ l1_pre_topc(X1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_11]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_14930,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(sK2),X0)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.39/1.53      | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13210]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_14932,plain,
% 7.39/1.53      ( ~ v1_tops_2(u1_pre_topc(sK2),sK1)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.39/1.53      | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
% 7.39/1.53      | ~ l1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_14930]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_3,plain,
% 7.39/1.53      ( ~ r2_hidden(X0,X1)
% 7.39/1.53      | m1_subset_1(X0,X2)
% 7.39/1.53      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.39/1.53      inference(cnf_transformation,[],[f45]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_7198,plain,
% 7.39/1.53      ( ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | m1_subset_1(sK0(sK2),X0)
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X0)) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_3]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_7343,plain,
% 7.39/1.53      ( ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_7198]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_7345,plain,
% 7.39/1.53      ( ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.39/1.53      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_7343]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_18,plain,
% 7.39/1.53      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.39/1.53      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 7.39/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.39/1.53      | ~ v3_tdlat_3(X1)
% 7.39/1.53      | ~ l1_pre_topc(X1) ),
% 7.39/1.53      inference(cnf_transformation,[],[f57]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_7330,plain,
% 7.39/1.53      ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.39/1.53      | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 7.39/1.53      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.39/1.53      | ~ v3_tdlat_3(X0)
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_18]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_7332,plain,
% 7.39/1.53      ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.39/1.53      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 7.39/1.53      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.39/1.53      | ~ v3_tdlat_3(sK1)
% 7.39/1.53      | ~ l1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_7330]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_15,plain,
% 7.39/1.53      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 7.39/1.53      | v3_tdlat_3(X0)
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(cnf_transformation,[],[f60]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6476,plain,
% 7.39/1.53      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 7.39/1.53      | v3_tdlat_3(sK2)
% 7.39/1.53      | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_15]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_323,plain,
% 7.39/1.53      ( X0 != X1 | X2 != X3 | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
% 7.39/1.53      theory(equality) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5929,plain,
% 7.39/1.53      ( X0 != sK0(sK2)
% 7.39/1.53      | X1 != u1_struct_0(X2)
% 7.39/1.53      | k6_subset_1(X1,X0) = k6_subset_1(u1_struct_0(X2),sK0(sK2)) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_323]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5965,plain,
% 7.39/1.53      ( X0 != u1_struct_0(X1)
% 7.39/1.53      | k6_subset_1(X0,sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
% 7.39/1.53      | sK0(sK2) != sK0(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5929]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5966,plain,
% 7.39/1.53      ( X0 != u1_struct_0(X1)
% 7.39/1.53      | k6_subset_1(X0,sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2)) ),
% 7.39/1.53      inference(equality_resolution_simp,[status(thm)],[c_5965]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6082,plain,
% 7.39/1.53      ( k6_subset_1(u1_struct_0(X0),sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
% 7.39/1.53      | u1_struct_0(X0) != u1_struct_0(X1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5966]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6439,plain,
% 7.39/1.53      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.39/1.53      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_6082]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6440,plain,
% 7.39/1.53      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.39/1.53      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_6439]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_315,plain,
% 7.39/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.39/1.53      theory(equality) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5730,plain,
% 7.39/1.53      ( r2_hidden(X0,X1)
% 7.39/1.53      | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
% 7.39/1.53      | X0 != k6_subset_1(u1_struct_0(X2),sK0(sK2))
% 7.39/1.53      | X1 != u1_pre_topc(X2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_315]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5917,plain,
% 7.39/1.53      ( r2_hidden(k6_subset_1(X0,X1),X2)
% 7.39/1.53      | ~ r2_hidden(k6_subset_1(u1_struct_0(X3),sK0(sK2)),u1_pre_topc(X3))
% 7.39/1.53      | X2 != u1_pre_topc(X3)
% 7.39/1.53      | k6_subset_1(X0,X1) != k6_subset_1(u1_struct_0(X3),sK0(sK2)) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5730]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6085,plain,
% 7.39/1.53      ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),X1)
% 7.39/1.53      | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
% 7.39/1.53      | X1 != u1_pre_topc(X2)
% 7.39/1.53      | k6_subset_1(u1_struct_0(X0),sK0(sK2)) != k6_subset_1(u1_struct_0(X2),sK0(sK2)) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5917]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6125,plain,
% 7.39/1.53      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.39/1.53      | r2_hidden(k6_subset_1(u1_struct_0(X1),sK0(sK2)),u1_pre_topc(X2))
% 7.39/1.53      | k6_subset_1(u1_struct_0(X1),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.39/1.53      | u1_pre_topc(X2) != u1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_6085]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6350,plain,
% 7.39/1.53      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.39/1.53      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 7.39/1.53      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.39/1.53      | u1_pre_topc(sK2) != u1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_6125]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_6352,plain,
% 7.39/1.53      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.39/1.53      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 7.39/1.53      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.39/1.53      | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_6350]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5052,plain,
% 7.39/1.53      ( ~ r1_tarski(X0,u1_pre_topc(X1))
% 7.39/1.53      | ~ r1_tarski(u1_pre_topc(X1),X0)
% 7.39/1.53      | X0 = u1_pre_topc(X1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_0]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5198,plain,
% 7.39/1.53      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 7.39/1.53      | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
% 7.39/1.53      | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5052]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5379,plain,
% 7.39/1.53      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 7.39/1.53      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
% 7.39/1.53      | u1_pre_topc(sK2) = u1_pre_topc(X0) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5198]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5381,plain,
% 7.39/1.53      ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
% 7.39/1.53      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
% 7.39/1.53      | u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5379]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5372,plain,
% 7.39/1.53      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 7.39/1.53      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
% 7.39/1.53      | u1_pre_topc(X0) = u1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5198]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5374,plain,
% 7.39/1.53      ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
% 7.39/1.53      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
% 7.39/1.53      | u1_pre_topc(sK1) = u1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5372]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_4986,plain,
% 7.39/1.53      ( r2_hidden(X0,X1)
% 7.39/1.53      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | X0 != sK0(sK2)
% 7.39/1.53      | X1 != u1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_315]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5008,plain,
% 7.39/1.53      ( r2_hidden(sK0(sK2),X0)
% 7.39/1.53      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | X0 != u1_pre_topc(sK2)
% 7.39/1.53      | sK0(sK2) != sK0(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_4986]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5009,plain,
% 7.39/1.53      ( r2_hidden(sK0(sK2),X0)
% 7.39/1.53      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | X0 != u1_pre_topc(sK2) ),
% 7.39/1.53      inference(equality_resolution_simp,[status(thm)],[c_5008]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5076,plain,
% 7.39/1.53      ( r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 7.39/1.53      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | u1_pre_topc(X0) != u1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5009]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_5078,plain,
% 7.39/1.53      ( r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 7.39/1.53      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | u1_pre_topc(sK1) != u1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5076]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_16,plain,
% 7.39/1.53      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 7.39/1.53      | v3_tdlat_3(X0)
% 7.39/1.53      | ~ l1_pre_topc(X0) ),
% 7.39/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_4025,plain,
% 7.39/1.53      ( r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.39/1.53      | v3_tdlat_3(sK2)
% 7.39/1.53      | ~ l1_pre_topc(sK2) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_16]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_56,plain,
% 7.39/1.53      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.39/1.53      | ~ l1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_41,plain,
% 7.39/1.53      ( v1_tops_2(u1_pre_topc(sK1),sK1) | ~ l1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_12]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_37,plain,
% 7.39/1.53      ( m1_pre_topc(X0,X0) = iProver_top
% 7.39/1.53      | l1_pre_topc(X0) != iProver_top ),
% 7.39/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_39,plain,
% 7.39/1.53      ( m1_pre_topc(sK1,sK1) = iProver_top
% 7.39/1.53      | l1_pre_topc(sK1) != iProver_top ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_37]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_38,plain,
% 7.39/1.53      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 7.39/1.53      inference(instantiation,[status(thm)],[c_13]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_19,negated_conjecture,
% 7.39/1.53      ( ~ v3_tdlat_3(sK2) ),
% 7.39/1.53      inference(cnf_transformation,[],[f65]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(c_20,negated_conjecture,
% 7.39/1.53      ( v3_tdlat_3(sK1) ),
% 7.39/1.53      inference(cnf_transformation,[],[f64]) ).
% 7.39/1.53  
% 7.39/1.53  cnf(contradiction,plain,
% 7.39/1.53      ( $false ),
% 7.39/1.53      inference(minisat,
% 7.39/1.53                [status(thm)],
% 7.39/1.53                [c_30377,c_29062,c_26060,c_26059,c_24982,c_24868,c_24393,
% 7.39/1.53                 c_24378,c_18766,c_18749,c_18248,c_17943,c_17521,c_17215,
% 7.39/1.53                 c_14932,c_7345,c_7332,c_6476,c_6440,c_6352,c_5381,
% 7.39/1.53                 c_5374,c_5078,c_4025,c_56,c_41,c_39,c_38,c_19,c_20,c_25,
% 7.39/1.53                 c_22,c_24,c_23]) ).
% 7.39/1.53  
% 7.39/1.53  
% 7.39/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.39/1.53  
% 7.39/1.53  ------                               Statistics
% 7.39/1.53  
% 7.39/1.53  ------ Selected
% 7.39/1.53  
% 7.39/1.53  total_time:                             0.72
% 7.39/1.53  
%------------------------------------------------------------------------------
