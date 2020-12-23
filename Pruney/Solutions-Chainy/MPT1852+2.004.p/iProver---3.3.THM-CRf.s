%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:33 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  253 (1576 expanded)
%              Number of clauses        :  183 ( 607 expanded)
%              Number of leaves         :   24 ( 339 expanded)
%              Depth                    :   32
%              Number of atoms          :  816 (6064 expanded)
%              Number of equality atoms :  333 (1555 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
        & r2_hidden(sK0(X0),u1_pre_topc(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f63,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( ~ v3_tdlat_3(sK2)
    & v3_tdlat_3(sK1)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f43,f42])).

fof(f69,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | r2_hidden(sK0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_831,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1468,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
    | u1_pre_topc(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1507,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
    | u1_pre_topc(sK2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_9625,plain,
    ( ~ r2_hidden(k6_subset_1(X0,X1),u1_pre_topc(X2))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
    | u1_pre_topc(sK2) != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_39605,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_pre_topc(sK2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_9625])).

cnf(c_39607,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_39605])).

cnf(c_830,plain,
    ( X0 != X1
    | X2 != X3
    | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_11664,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,X1)
    | sK0(sK2) != X1
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_17016,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_11664])).

cnf(c_26646,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_17016])).

cnf(c_26647,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_26646])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22830,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_22837,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22830])).

cnf(c_9865,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,u1_pre_topc(X3))
    | X2 != X0
    | u1_pre_topc(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_11879,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | X0 != sK0(sK2)
    | u1_pre_topc(X1) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9865])).

cnf(c_15732,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_pre_topc(X0) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_11879])).

cnf(c_15734,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_pre_topc(sK1) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_15732])).

cnf(c_819,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3410,plain,
    ( X0 != X1
    | X0 = u1_pre_topc(X2)
    | u1_pre_topc(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_4402,plain,
    ( X0 != u1_pre_topc(X1)
    | X0 = u1_pre_topc(X2)
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_3410])).

cnf(c_5933,plain,
    ( u1_pre_topc(X0) != u1_pre_topc(X0)
    | u1_pre_topc(X1) != u1_pre_topc(X0)
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_4402])).

cnf(c_8641,plain,
    ( u1_pre_topc(X0) != u1_pre_topc(X0)
    | u1_pre_topc(X0) = u1_pre_topc(sK2)
    | u1_pre_topc(sK2) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_5933])).

cnf(c_8642,plain,
    ( u1_pre_topc(sK1) != u1_pre_topc(sK1)
    | u1_pre_topc(sK1) = u1_pre_topc(sK2)
    | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8641])).

cnf(c_6,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1419,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1416,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2761,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_1416])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_63,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3510,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2761,c_63])).

cnf(c_3511,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3510])).

cnf(c_14,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1413,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3518,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3511,c_1413])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1410,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1417,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2241,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1417])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2329,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2241,c_27])).

cnf(c_2330,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2329])).

cnf(c_2336,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_2330])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_145,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_5])).

cnf(c_146,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_1401,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_2335,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_2330])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2416,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2335,c_28])).

cnf(c_2417,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2416])).

cnf(c_2422,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_2417])).

cnf(c_2576,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2422,c_28])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1411,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1418,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2719,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1418])).

cnf(c_3818,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2576,c_2719])).

cnf(c_4468,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3818,c_27])).

cnf(c_4469,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4468])).

cnf(c_4473,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4469,c_1418])).

cnf(c_5840,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4473,c_63])).

cnf(c_5841,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5840])).

cnf(c_5852,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2336,c_5841])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_39,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_3829,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3818])).

cnf(c_6116,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5852,c_27,c_39,c_3829])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6120,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6116,c_1421])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1424,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6522,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6120,c_1424])).

cnf(c_2182,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2183,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2182])).

cnf(c_1762,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1401])).

cnf(c_1915,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1762,c_27])).

cnf(c_1916,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1915])).

cnf(c_2240,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_1417])).

cnf(c_2343,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2240,c_28])).

cnf(c_2344,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2343])).

cnf(c_2349,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_2344])).

cnf(c_2246,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2240])).

cnf(c_2494,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2349,c_27,c_28,c_39,c_2246])).

cnf(c_3821,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2494,c_2719])).

cnf(c_4479,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3821,c_28])).

cnf(c_4480,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4479])).

cnf(c_4485,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4480,c_1421])).

cnf(c_4472,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4469,c_1421])).

cnf(c_4590,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK2)
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4472,c_1424])).

cnf(c_4698,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4485,c_4590])).

cnf(c_6602,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6522,c_27,c_28,c_39,c_2183,c_4698])).

cnf(c_6653,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6602,c_1419])).

cnf(c_60,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_62,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_2084,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2463,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_2464,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2463])).

cnf(c_2466,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_7072,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6653,c_27,c_28,c_39,c_62,c_2246,c_2466])).

cnf(c_7081,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK2) != iProver_top
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7072,c_1413])).

cnf(c_15,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_43,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_45,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_12,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1633,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,sK2)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2788,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X1)
    | v1_tops_2(u1_pre_topc(X0),sK2)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_2799,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
    | v1_tops_2(u1_pre_topc(X0),sK2) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2788])).

cnf(c_2801,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1) != iProver_top
    | v1_tops_2(u1_pre_topc(sK1),sK2) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2799])).

cnf(c_1545,plain,
    ( ~ v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(X0,u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3056,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),sK2)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_3057,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK2) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3056])).

cnf(c_3059,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK2) != iProver_top
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3057])).

cnf(c_8459,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7081,c_27,c_28,c_39,c_45,c_62,c_2246,c_2422,c_2466,c_2801,c_3059])).

cnf(c_8463,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK1)
    | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8459,c_1424])).

cnf(c_8467,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK1)
    | v1_tops_2(u1_pre_topc(sK2),sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_8463])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3107,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != sK0(sK2)
    | X1 != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_3597,plain,
    ( m1_subset_1(sK0(sK2),X0)
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK2))
    | sK0(sK2) != sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_3107])).

cnf(c_4649,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2) != sK0(sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3597])).

cnf(c_7924,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2) != sK0(sK2)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4649])).

cnf(c_7931,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2) != sK0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_7924])).

cnf(c_7468,plain,
    ( v1_tops_2(u1_pre_topc(sK2),X0)
    | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7469,plain,
    ( v1_tops_2(u1_pre_topc(sK2),X0) = iProver_top
    | v1_tops_2(u1_pre_topc(sK2),sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7468])).

cnf(c_7471,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK1) = iProver_top
    | v1_tops_2(u1_pre_topc(sK2),sK2) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7469])).

cnf(c_2772,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5236,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_5238,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_5236])).

cnf(c_3474,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(X1)),X0)
    | k1_zfmisc_1(u1_struct_0(X1)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4421,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(X0)))
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_4423,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4421])).

cnf(c_4152,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_4154,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4152])).

cnf(c_3392,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_3394,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3392])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3363,plain,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3365,plain,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_2860,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2862,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2860])).

cnf(c_2844,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2845,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2844])).

cnf(c_2847,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2845])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2458,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2777,plain,
    ( m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_2779,plain,
    ( m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_2476,plain,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2423,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2422])).

cnf(c_2078,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2271,plain,
    ( m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_2245,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2240])).

cnf(c_2247,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_818,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2128,plain,
    ( sK0(sK2) = sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1881,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1882,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_1718,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1719,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1718])).

cnf(c_825,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_837,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_18,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_413,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_414,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_19,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_402,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_403,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_20,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_391,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_392,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_75,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_71,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_38,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_23,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39607,c_26647,c_22837,c_15734,c_8642,c_8467,c_7931,c_7471,c_5238,c_4698,c_4423,c_4154,c_3394,c_3365,c_2862,c_2847,c_2779,c_2476,c_2423,c_2422,c_2271,c_2247,c_2246,c_2183,c_2128,c_1882,c_1719,c_837,c_414,c_403,c_392,c_75,c_71,c_39,c_38,c_23,c_28,c_25,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.03/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.03/1.48  
% 8.03/1.48  ------  iProver source info
% 8.03/1.48  
% 8.03/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.03/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.03/1.48  git: non_committed_changes: false
% 8.03/1.48  git: last_make_outside_of_git: false
% 8.03/1.48  
% 8.03/1.48  ------ 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options
% 8.03/1.48  
% 8.03/1.48  --out_options                           all
% 8.03/1.48  --tptp_safe_out                         true
% 8.03/1.48  --problem_path                          ""
% 8.03/1.48  --include_path                          ""
% 8.03/1.48  --clausifier                            res/vclausify_rel
% 8.03/1.48  --clausifier_options                    ""
% 8.03/1.48  --stdin                                 false
% 8.03/1.48  --stats_out                             all
% 8.03/1.48  
% 8.03/1.48  ------ General Options
% 8.03/1.48  
% 8.03/1.48  --fof                                   false
% 8.03/1.48  --time_out_real                         305.
% 8.03/1.48  --time_out_virtual                      -1.
% 8.03/1.48  --symbol_type_check                     false
% 8.03/1.48  --clausify_out                          false
% 8.03/1.48  --sig_cnt_out                           false
% 8.03/1.48  --trig_cnt_out                          false
% 8.03/1.48  --trig_cnt_out_tolerance                1.
% 8.03/1.48  --trig_cnt_out_sk_spl                   false
% 8.03/1.48  --abstr_cl_out                          false
% 8.03/1.48  
% 8.03/1.48  ------ Global Options
% 8.03/1.48  
% 8.03/1.48  --schedule                              default
% 8.03/1.48  --add_important_lit                     false
% 8.03/1.48  --prop_solver_per_cl                    1000
% 8.03/1.48  --min_unsat_core                        false
% 8.03/1.48  --soft_assumptions                      false
% 8.03/1.48  --soft_lemma_size                       3
% 8.03/1.48  --prop_impl_unit_size                   0
% 8.03/1.48  --prop_impl_unit                        []
% 8.03/1.48  --share_sel_clauses                     true
% 8.03/1.48  --reset_solvers                         false
% 8.03/1.48  --bc_imp_inh                            [conj_cone]
% 8.03/1.48  --conj_cone_tolerance                   3.
% 8.03/1.48  --extra_neg_conj                        none
% 8.03/1.48  --large_theory_mode                     true
% 8.03/1.48  --prolific_symb_bound                   200
% 8.03/1.48  --lt_threshold                          2000
% 8.03/1.48  --clause_weak_htbl                      true
% 8.03/1.48  --gc_record_bc_elim                     false
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing Options
% 8.03/1.48  
% 8.03/1.48  --preprocessing_flag                    true
% 8.03/1.48  --time_out_prep_mult                    0.1
% 8.03/1.48  --splitting_mode                        input
% 8.03/1.48  --splitting_grd                         true
% 8.03/1.48  --splitting_cvd                         false
% 8.03/1.48  --splitting_cvd_svl                     false
% 8.03/1.48  --splitting_nvd                         32
% 8.03/1.48  --sub_typing                            true
% 8.03/1.48  --prep_gs_sim                           true
% 8.03/1.48  --prep_unflatten                        true
% 8.03/1.48  --prep_res_sim                          true
% 8.03/1.48  --prep_upred                            true
% 8.03/1.48  --prep_sem_filter                       exhaustive
% 8.03/1.48  --prep_sem_filter_out                   false
% 8.03/1.48  --pred_elim                             true
% 8.03/1.48  --res_sim_input                         true
% 8.03/1.48  --eq_ax_congr_red                       true
% 8.03/1.48  --pure_diseq_elim                       true
% 8.03/1.48  --brand_transform                       false
% 8.03/1.48  --non_eq_to_eq                          false
% 8.03/1.48  --prep_def_merge                        true
% 8.03/1.48  --prep_def_merge_prop_impl              false
% 8.03/1.48  --prep_def_merge_mbd                    true
% 8.03/1.48  --prep_def_merge_tr_red                 false
% 8.03/1.48  --prep_def_merge_tr_cl                  false
% 8.03/1.48  --smt_preprocessing                     true
% 8.03/1.48  --smt_ac_axioms                         fast
% 8.03/1.48  --preprocessed_out                      false
% 8.03/1.48  --preprocessed_stats                    false
% 8.03/1.48  
% 8.03/1.48  ------ Abstraction refinement Options
% 8.03/1.48  
% 8.03/1.48  --abstr_ref                             []
% 8.03/1.48  --abstr_ref_prep                        false
% 8.03/1.48  --abstr_ref_until_sat                   false
% 8.03/1.48  --abstr_ref_sig_restrict                funpre
% 8.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.48  --abstr_ref_under                       []
% 8.03/1.48  
% 8.03/1.48  ------ SAT Options
% 8.03/1.48  
% 8.03/1.48  --sat_mode                              false
% 8.03/1.48  --sat_fm_restart_options                ""
% 8.03/1.48  --sat_gr_def                            false
% 8.03/1.48  --sat_epr_types                         true
% 8.03/1.48  --sat_non_cyclic_types                  false
% 8.03/1.48  --sat_finite_models                     false
% 8.03/1.48  --sat_fm_lemmas                         false
% 8.03/1.48  --sat_fm_prep                           false
% 8.03/1.48  --sat_fm_uc_incr                        true
% 8.03/1.48  --sat_out_model                         small
% 8.03/1.48  --sat_out_clauses                       false
% 8.03/1.48  
% 8.03/1.48  ------ QBF Options
% 8.03/1.48  
% 8.03/1.48  --qbf_mode                              false
% 8.03/1.48  --qbf_elim_univ                         false
% 8.03/1.48  --qbf_dom_inst                          none
% 8.03/1.48  --qbf_dom_pre_inst                      false
% 8.03/1.48  --qbf_sk_in                             false
% 8.03/1.48  --qbf_pred_elim                         true
% 8.03/1.48  --qbf_split                             512
% 8.03/1.48  
% 8.03/1.48  ------ BMC1 Options
% 8.03/1.48  
% 8.03/1.48  --bmc1_incremental                      false
% 8.03/1.48  --bmc1_axioms                           reachable_all
% 8.03/1.48  --bmc1_min_bound                        0
% 8.03/1.48  --bmc1_max_bound                        -1
% 8.03/1.48  --bmc1_max_bound_default                -1
% 8.03/1.48  --bmc1_symbol_reachability              true
% 8.03/1.48  --bmc1_property_lemmas                  false
% 8.03/1.48  --bmc1_k_induction                      false
% 8.03/1.48  --bmc1_non_equiv_states                 false
% 8.03/1.48  --bmc1_deadlock                         false
% 8.03/1.48  --bmc1_ucm                              false
% 8.03/1.48  --bmc1_add_unsat_core                   none
% 8.03/1.48  --bmc1_unsat_core_children              false
% 8.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.48  --bmc1_out_stat                         full
% 8.03/1.48  --bmc1_ground_init                      false
% 8.03/1.48  --bmc1_pre_inst_next_state              false
% 8.03/1.48  --bmc1_pre_inst_state                   false
% 8.03/1.48  --bmc1_pre_inst_reach_state             false
% 8.03/1.48  --bmc1_out_unsat_core                   false
% 8.03/1.48  --bmc1_aig_witness_out                  false
% 8.03/1.48  --bmc1_verbose                          false
% 8.03/1.48  --bmc1_dump_clauses_tptp                false
% 8.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.48  --bmc1_dump_file                        -
% 8.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.48  --bmc1_ucm_extend_mode                  1
% 8.03/1.48  --bmc1_ucm_init_mode                    2
% 8.03/1.48  --bmc1_ucm_cone_mode                    none
% 8.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.48  --bmc1_ucm_relax_model                  4
% 8.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.48  --bmc1_ucm_layered_model                none
% 8.03/1.48  --bmc1_ucm_max_lemma_size               10
% 8.03/1.48  
% 8.03/1.48  ------ AIG Options
% 8.03/1.48  
% 8.03/1.48  --aig_mode                              false
% 8.03/1.48  
% 8.03/1.48  ------ Instantiation Options
% 8.03/1.48  
% 8.03/1.48  --instantiation_flag                    true
% 8.03/1.48  --inst_sos_flag                         true
% 8.03/1.48  --inst_sos_phase                        true
% 8.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel_side                     num_symb
% 8.03/1.48  --inst_solver_per_active                1400
% 8.03/1.48  --inst_solver_calls_frac                1.
% 8.03/1.48  --inst_passive_queue_type               priority_queues
% 8.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.48  --inst_passive_queues_freq              [25;2]
% 8.03/1.48  --inst_dismatching                      true
% 8.03/1.48  --inst_eager_unprocessed_to_passive     true
% 8.03/1.48  --inst_prop_sim_given                   true
% 8.03/1.48  --inst_prop_sim_new                     false
% 8.03/1.48  --inst_subs_new                         false
% 8.03/1.48  --inst_eq_res_simp                      false
% 8.03/1.48  --inst_subs_given                       false
% 8.03/1.48  --inst_orphan_elimination               true
% 8.03/1.48  --inst_learning_loop_flag               true
% 8.03/1.48  --inst_learning_start                   3000
% 8.03/1.48  --inst_learning_factor                  2
% 8.03/1.48  --inst_start_prop_sim_after_learn       3
% 8.03/1.48  --inst_sel_renew                        solver
% 8.03/1.48  --inst_lit_activity_flag                true
% 8.03/1.48  --inst_restr_to_given                   false
% 8.03/1.48  --inst_activity_threshold               500
% 8.03/1.48  --inst_out_proof                        true
% 8.03/1.48  
% 8.03/1.48  ------ Resolution Options
% 8.03/1.48  
% 8.03/1.48  --resolution_flag                       true
% 8.03/1.48  --res_lit_sel                           adaptive
% 8.03/1.48  --res_lit_sel_side                      none
% 8.03/1.48  --res_ordering                          kbo
% 8.03/1.48  --res_to_prop_solver                    active
% 8.03/1.48  --res_prop_simpl_new                    false
% 8.03/1.48  --res_prop_simpl_given                  true
% 8.03/1.48  --res_passive_queue_type                priority_queues
% 8.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.48  --res_passive_queues_freq               [15;5]
% 8.03/1.48  --res_forward_subs                      full
% 8.03/1.48  --res_backward_subs                     full
% 8.03/1.48  --res_forward_subs_resolution           true
% 8.03/1.48  --res_backward_subs_resolution          true
% 8.03/1.48  --res_orphan_elimination                true
% 8.03/1.48  --res_time_limit                        2.
% 8.03/1.48  --res_out_proof                         true
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Options
% 8.03/1.48  
% 8.03/1.48  --superposition_flag                    true
% 8.03/1.48  --sup_passive_queue_type                priority_queues
% 8.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.48  --demod_completeness_check              fast
% 8.03/1.48  --demod_use_ground                      true
% 8.03/1.48  --sup_to_prop_solver                    passive
% 8.03/1.48  --sup_prop_simpl_new                    true
% 8.03/1.48  --sup_prop_simpl_given                  true
% 8.03/1.48  --sup_fun_splitting                     true
% 8.03/1.48  --sup_smt_interval                      50000
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Simplification Setup
% 8.03/1.48  
% 8.03/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_immed_triv                        [TrivRules]
% 8.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_bw_main                     []
% 8.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_input_bw                          []
% 8.03/1.48  
% 8.03/1.48  ------ Combination Options
% 8.03/1.48  
% 8.03/1.48  --comb_res_mult                         3
% 8.03/1.48  --comb_sup_mult                         2
% 8.03/1.48  --comb_inst_mult                        10
% 8.03/1.48  
% 8.03/1.48  ------ Debug Options
% 8.03/1.48  
% 8.03/1.48  --dbg_backtrace                         false
% 8.03/1.48  --dbg_dump_prop_clauses                 false
% 8.03/1.48  --dbg_dump_prop_clauses_file            -
% 8.03/1.48  --dbg_out_stat                          false
% 8.03/1.48  ------ Parsing...
% 8.03/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.48  ------ Proving...
% 8.03/1.48  ------ Problem Properties 
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  clauses                                 25
% 8.03/1.48  conjectures                             5
% 8.03/1.48  EPR                                     8
% 8.03/1.48  Horn                                    23
% 8.03/1.48  unary                                   6
% 8.03/1.48  binary                                  5
% 8.03/1.48  lits                                    67
% 8.03/1.48  lits eq                                 2
% 8.03/1.48  fd_pure                                 0
% 8.03/1.48  fd_pseudo                               0
% 8.03/1.48  fd_cond                                 0
% 8.03/1.48  fd_pseudo_cond                          1
% 8.03/1.48  AC symbols                              0
% 8.03/1.48  
% 8.03/1.48  ------ Schedule dynamic 5 is on 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  ------ 
% 8.03/1.48  Current options:
% 8.03/1.48  ------ 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options
% 8.03/1.48  
% 8.03/1.48  --out_options                           all
% 8.03/1.48  --tptp_safe_out                         true
% 8.03/1.48  --problem_path                          ""
% 8.03/1.48  --include_path                          ""
% 8.03/1.48  --clausifier                            res/vclausify_rel
% 8.03/1.48  --clausifier_options                    ""
% 8.03/1.48  --stdin                                 false
% 8.03/1.48  --stats_out                             all
% 8.03/1.48  
% 8.03/1.48  ------ General Options
% 8.03/1.48  
% 8.03/1.48  --fof                                   false
% 8.03/1.48  --time_out_real                         305.
% 8.03/1.48  --time_out_virtual                      -1.
% 8.03/1.48  --symbol_type_check                     false
% 8.03/1.48  --clausify_out                          false
% 8.03/1.48  --sig_cnt_out                           false
% 8.03/1.48  --trig_cnt_out                          false
% 8.03/1.48  --trig_cnt_out_tolerance                1.
% 8.03/1.48  --trig_cnt_out_sk_spl                   false
% 8.03/1.48  --abstr_cl_out                          false
% 8.03/1.48  
% 8.03/1.48  ------ Global Options
% 8.03/1.48  
% 8.03/1.48  --schedule                              default
% 8.03/1.48  --add_important_lit                     false
% 8.03/1.48  --prop_solver_per_cl                    1000
% 8.03/1.48  --min_unsat_core                        false
% 8.03/1.48  --soft_assumptions                      false
% 8.03/1.48  --soft_lemma_size                       3
% 8.03/1.48  --prop_impl_unit_size                   0
% 8.03/1.48  --prop_impl_unit                        []
% 8.03/1.48  --share_sel_clauses                     true
% 8.03/1.48  --reset_solvers                         false
% 8.03/1.48  --bc_imp_inh                            [conj_cone]
% 8.03/1.48  --conj_cone_tolerance                   3.
% 8.03/1.48  --extra_neg_conj                        none
% 8.03/1.48  --large_theory_mode                     true
% 8.03/1.48  --prolific_symb_bound                   200
% 8.03/1.48  --lt_threshold                          2000
% 8.03/1.48  --clause_weak_htbl                      true
% 8.03/1.48  --gc_record_bc_elim                     false
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing Options
% 8.03/1.48  
% 8.03/1.48  --preprocessing_flag                    true
% 8.03/1.48  --time_out_prep_mult                    0.1
% 8.03/1.48  --splitting_mode                        input
% 8.03/1.48  --splitting_grd                         true
% 8.03/1.48  --splitting_cvd                         false
% 8.03/1.48  --splitting_cvd_svl                     false
% 8.03/1.48  --splitting_nvd                         32
% 8.03/1.48  --sub_typing                            true
% 8.03/1.48  --prep_gs_sim                           true
% 8.03/1.48  --prep_unflatten                        true
% 8.03/1.48  --prep_res_sim                          true
% 8.03/1.48  --prep_upred                            true
% 8.03/1.48  --prep_sem_filter                       exhaustive
% 8.03/1.48  --prep_sem_filter_out                   false
% 8.03/1.48  --pred_elim                             true
% 8.03/1.48  --res_sim_input                         true
% 8.03/1.48  --eq_ax_congr_red                       true
% 8.03/1.48  --pure_diseq_elim                       true
% 8.03/1.48  --brand_transform                       false
% 8.03/1.48  --non_eq_to_eq                          false
% 8.03/1.48  --prep_def_merge                        true
% 8.03/1.48  --prep_def_merge_prop_impl              false
% 8.03/1.48  --prep_def_merge_mbd                    true
% 8.03/1.48  --prep_def_merge_tr_red                 false
% 8.03/1.48  --prep_def_merge_tr_cl                  false
% 8.03/1.48  --smt_preprocessing                     true
% 8.03/1.48  --smt_ac_axioms                         fast
% 8.03/1.48  --preprocessed_out                      false
% 8.03/1.48  --preprocessed_stats                    false
% 8.03/1.48  
% 8.03/1.48  ------ Abstraction refinement Options
% 8.03/1.48  
% 8.03/1.48  --abstr_ref                             []
% 8.03/1.48  --abstr_ref_prep                        false
% 8.03/1.48  --abstr_ref_until_sat                   false
% 8.03/1.48  --abstr_ref_sig_restrict                funpre
% 8.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.48  --abstr_ref_under                       []
% 8.03/1.48  
% 8.03/1.48  ------ SAT Options
% 8.03/1.48  
% 8.03/1.48  --sat_mode                              false
% 8.03/1.48  --sat_fm_restart_options                ""
% 8.03/1.48  --sat_gr_def                            false
% 8.03/1.48  --sat_epr_types                         true
% 8.03/1.48  --sat_non_cyclic_types                  false
% 8.03/1.48  --sat_finite_models                     false
% 8.03/1.48  --sat_fm_lemmas                         false
% 8.03/1.48  --sat_fm_prep                           false
% 8.03/1.48  --sat_fm_uc_incr                        true
% 8.03/1.48  --sat_out_model                         small
% 8.03/1.48  --sat_out_clauses                       false
% 8.03/1.48  
% 8.03/1.48  ------ QBF Options
% 8.03/1.48  
% 8.03/1.48  --qbf_mode                              false
% 8.03/1.48  --qbf_elim_univ                         false
% 8.03/1.48  --qbf_dom_inst                          none
% 8.03/1.48  --qbf_dom_pre_inst                      false
% 8.03/1.48  --qbf_sk_in                             false
% 8.03/1.48  --qbf_pred_elim                         true
% 8.03/1.48  --qbf_split                             512
% 8.03/1.48  
% 8.03/1.48  ------ BMC1 Options
% 8.03/1.48  
% 8.03/1.48  --bmc1_incremental                      false
% 8.03/1.48  --bmc1_axioms                           reachable_all
% 8.03/1.48  --bmc1_min_bound                        0
% 8.03/1.48  --bmc1_max_bound                        -1
% 8.03/1.48  --bmc1_max_bound_default                -1
% 8.03/1.48  --bmc1_symbol_reachability              true
% 8.03/1.48  --bmc1_property_lemmas                  false
% 8.03/1.48  --bmc1_k_induction                      false
% 8.03/1.48  --bmc1_non_equiv_states                 false
% 8.03/1.48  --bmc1_deadlock                         false
% 8.03/1.48  --bmc1_ucm                              false
% 8.03/1.48  --bmc1_add_unsat_core                   none
% 8.03/1.48  --bmc1_unsat_core_children              false
% 8.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.48  --bmc1_out_stat                         full
% 8.03/1.48  --bmc1_ground_init                      false
% 8.03/1.48  --bmc1_pre_inst_next_state              false
% 8.03/1.48  --bmc1_pre_inst_state                   false
% 8.03/1.48  --bmc1_pre_inst_reach_state             false
% 8.03/1.48  --bmc1_out_unsat_core                   false
% 8.03/1.48  --bmc1_aig_witness_out                  false
% 8.03/1.48  --bmc1_verbose                          false
% 8.03/1.48  --bmc1_dump_clauses_tptp                false
% 8.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.48  --bmc1_dump_file                        -
% 8.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.48  --bmc1_ucm_extend_mode                  1
% 8.03/1.48  --bmc1_ucm_init_mode                    2
% 8.03/1.48  --bmc1_ucm_cone_mode                    none
% 8.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.48  --bmc1_ucm_relax_model                  4
% 8.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.48  --bmc1_ucm_layered_model                none
% 8.03/1.48  --bmc1_ucm_max_lemma_size               10
% 8.03/1.48  
% 8.03/1.48  ------ AIG Options
% 8.03/1.48  
% 8.03/1.48  --aig_mode                              false
% 8.03/1.48  
% 8.03/1.48  ------ Instantiation Options
% 8.03/1.48  
% 8.03/1.48  --instantiation_flag                    true
% 8.03/1.48  --inst_sos_flag                         true
% 8.03/1.48  --inst_sos_phase                        true
% 8.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel_side                     none
% 8.03/1.48  --inst_solver_per_active                1400
% 8.03/1.48  --inst_solver_calls_frac                1.
% 8.03/1.48  --inst_passive_queue_type               priority_queues
% 8.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.48  --inst_passive_queues_freq              [25;2]
% 8.03/1.48  --inst_dismatching                      true
% 8.03/1.48  --inst_eager_unprocessed_to_passive     true
% 8.03/1.48  --inst_prop_sim_given                   true
% 8.03/1.48  --inst_prop_sim_new                     false
% 8.03/1.48  --inst_subs_new                         false
% 8.03/1.48  --inst_eq_res_simp                      false
% 8.03/1.48  --inst_subs_given                       false
% 8.03/1.48  --inst_orphan_elimination               true
% 8.03/1.48  --inst_learning_loop_flag               true
% 8.03/1.48  --inst_learning_start                   3000
% 8.03/1.48  --inst_learning_factor                  2
% 8.03/1.48  --inst_start_prop_sim_after_learn       3
% 8.03/1.48  --inst_sel_renew                        solver
% 8.03/1.48  --inst_lit_activity_flag                true
% 8.03/1.48  --inst_restr_to_given                   false
% 8.03/1.48  --inst_activity_threshold               500
% 8.03/1.48  --inst_out_proof                        true
% 8.03/1.48  
% 8.03/1.48  ------ Resolution Options
% 8.03/1.48  
% 8.03/1.48  --resolution_flag                       false
% 8.03/1.48  --res_lit_sel                           adaptive
% 8.03/1.48  --res_lit_sel_side                      none
% 8.03/1.48  --res_ordering                          kbo
% 8.03/1.48  --res_to_prop_solver                    active
% 8.03/1.48  --res_prop_simpl_new                    false
% 8.03/1.48  --res_prop_simpl_given                  true
% 8.03/1.48  --res_passive_queue_type                priority_queues
% 8.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.48  --res_passive_queues_freq               [15;5]
% 8.03/1.48  --res_forward_subs                      full
% 8.03/1.48  --res_backward_subs                     full
% 8.03/1.48  --res_forward_subs_resolution           true
% 8.03/1.48  --res_backward_subs_resolution          true
% 8.03/1.48  --res_orphan_elimination                true
% 8.03/1.48  --res_time_limit                        2.
% 8.03/1.48  --res_out_proof                         true
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Options
% 8.03/1.48  
% 8.03/1.48  --superposition_flag                    true
% 8.03/1.48  --sup_passive_queue_type                priority_queues
% 8.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.48  --demod_completeness_check              fast
% 8.03/1.48  --demod_use_ground                      true
% 8.03/1.48  --sup_to_prop_solver                    passive
% 8.03/1.48  --sup_prop_simpl_new                    true
% 8.03/1.48  --sup_prop_simpl_given                  true
% 8.03/1.48  --sup_fun_splitting                     true
% 8.03/1.48  --sup_smt_interval                      50000
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Simplification Setup
% 8.03/1.48  
% 8.03/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_immed_triv                        [TrivRules]
% 8.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_bw_main                     []
% 8.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_input_bw                          []
% 8.03/1.48  
% 8.03/1.48  ------ Combination Options
% 8.03/1.48  
% 8.03/1.48  --comb_res_mult                         3
% 8.03/1.48  --comb_sup_mult                         2
% 8.03/1.48  --comb_inst_mult                        10
% 8.03/1.48  
% 8.03/1.48  ------ Debug Options
% 8.03/1.48  
% 8.03/1.48  --dbg_backtrace                         false
% 8.03/1.48  --dbg_dump_prop_clauses                 false
% 8.03/1.48  --dbg_dump_prop_clauses_file            -
% 8.03/1.48  --dbg_out_stat                          false
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  ------ Proving...
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  % SZS status Theorem for theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  fof(f14,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f29,plain,(
% 8.03/1.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f14])).
% 8.03/1.48  
% 8.03/1.48  fof(f30,plain,(
% 8.03/1.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(flattening,[],[f29])).
% 8.03/1.48  
% 8.03/1.48  fof(f38,plain,(
% 8.03/1.48    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(nnf_transformation,[],[f30])).
% 8.03/1.48  
% 8.03/1.48  fof(f39,plain,(
% 8.03/1.48    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(rectify,[],[f38])).
% 8.03/1.48  
% 8.03/1.48  fof(f40,plain,(
% 8.03/1.48    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.03/1.48    introduced(choice_axiom,[])).
% 8.03/1.48  
% 8.03/1.48  fof(f41,plain,(
% 8.03/1.48    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 8.03/1.48  
% 8.03/1.48  fof(f63,plain,(
% 8.03/1.48    ( ! [X2,X0] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f41])).
% 8.03/1.48  
% 8.03/1.48  fof(f4,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f18,plain,(
% 8.03/1.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f4])).
% 8.03/1.48  
% 8.03/1.48  fof(f51,plain,(
% 8.03/1.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f18])).
% 8.03/1.48  
% 8.03/1.48  fof(f8,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f22,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f8])).
% 8.03/1.48  
% 8.03/1.48  fof(f56,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f22])).
% 8.03/1.48  
% 8.03/1.48  fof(f3,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f17,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f3])).
% 8.03/1.48  
% 8.03/1.48  fof(f50,plain,(
% 8.03/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f17])).
% 8.03/1.48  
% 8.03/1.48  fof(f10,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f25,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f10])).
% 8.03/1.48  
% 8.03/1.48  fof(f37,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(nnf_transformation,[],[f25])).
% 8.03/1.48  
% 8.03/1.48  fof(f58,plain,(
% 8.03/1.48    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f37])).
% 8.03/1.48  
% 8.03/1.48  fof(f13,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f28,plain,(
% 8.03/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f13])).
% 8.03/1.48  
% 8.03/1.48  fof(f62,plain,(
% 8.03/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f28])).
% 8.03/1.48  
% 8.03/1.48  fof(f15,conjecture,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f16,negated_conjecture,(
% 8.03/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 8.03/1.48    inference(negated_conjecture,[],[f15])).
% 8.03/1.48  
% 8.03/1.48  fof(f31,plain,(
% 8.03/1.48    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f16])).
% 8.03/1.48  
% 8.03/1.48  fof(f32,plain,(
% 8.03/1.48    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 8.03/1.48    inference(flattening,[],[f31])).
% 8.03/1.48  
% 8.03/1.48  fof(f43,plain,(
% 8.03/1.48    ( ! [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK2) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK2))) )),
% 8.03/1.48    introduced(choice_axiom,[])).
% 8.03/1.48  
% 8.03/1.48  fof(f42,plain,(
% 8.03/1.48    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK1))),
% 8.03/1.48    introduced(choice_axiom,[])).
% 8.03/1.48  
% 8.03/1.48  fof(f44,plain,(
% 8.03/1.48    (~v3_tdlat_3(sK2) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2)) & l1_pre_topc(sK1)),
% 8.03/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f43,f42])).
% 8.03/1.48  
% 8.03/1.48  fof(f69,plain,(
% 8.03/1.48    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 8.03/1.48    inference(cnf_transformation,[],[f44])).
% 8.03/1.48  
% 8.03/1.48  fof(f6,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f20,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f6])).
% 8.03/1.48  
% 8.03/1.48  fof(f53,plain,(
% 8.03/1.48    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f20])).
% 8.03/1.48  
% 8.03/1.48  fof(f67,plain,(
% 8.03/1.48    l1_pre_topc(sK1)),
% 8.03/1.48    inference(cnf_transformation,[],[f44])).
% 8.03/1.48  
% 8.03/1.48  fof(f7,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f21,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f7])).
% 8.03/1.48  
% 8.03/1.48  fof(f36,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(nnf_transformation,[],[f21])).
% 8.03/1.48  
% 8.03/1.48  fof(f54,plain,(
% 8.03/1.48    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f36])).
% 8.03/1.48  
% 8.03/1.48  fof(f68,plain,(
% 8.03/1.48    l1_pre_topc(sK2)),
% 8.03/1.48    inference(cnf_transformation,[],[f44])).
% 8.03/1.48  
% 8.03/1.48  fof(f12,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f27,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f12])).
% 8.03/1.48  
% 8.03/1.48  fof(f61,plain,(
% 8.03/1.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f27])).
% 8.03/1.48  
% 8.03/1.48  fof(f5,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f19,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f5])).
% 8.03/1.48  
% 8.03/1.48  fof(f52,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f19])).
% 8.03/1.48  
% 8.03/1.48  fof(f2,axiom,(
% 8.03/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f35,plain,(
% 8.03/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.03/1.48    inference(nnf_transformation,[],[f2])).
% 8.03/1.48  
% 8.03/1.48  fof(f48,plain,(
% 8.03/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f35])).
% 8.03/1.48  
% 8.03/1.48  fof(f1,axiom,(
% 8.03/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f33,plain,(
% 8.03/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.03/1.48    inference(nnf_transformation,[],[f1])).
% 8.03/1.48  
% 8.03/1.48  fof(f34,plain,(
% 8.03/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.03/1.48    inference(flattening,[],[f33])).
% 8.03/1.48  
% 8.03/1.48  fof(f47,plain,(
% 8.03/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f34])).
% 8.03/1.48  
% 8.03/1.48  fof(f11,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f26,plain,(
% 8.03/1.48    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f11])).
% 8.03/1.48  
% 8.03/1.48  fof(f60,plain,(
% 8.03/1.48    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f26])).
% 8.03/1.48  
% 8.03/1.48  fof(f9,axiom,(
% 8.03/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f23,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f9])).
% 8.03/1.48  
% 8.03/1.48  fof(f24,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.03/1.49    inference(flattening,[],[f23])).
% 8.03/1.49  
% 8.03/1.49  fof(f57,plain,(
% 8.03/1.49    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.03/1.49    inference(cnf_transformation,[],[f24])).
% 8.03/1.49  
% 8.03/1.49  fof(f74,plain,(
% 8.03/1.49    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.03/1.49    inference(equality_resolution,[],[f57])).
% 8.03/1.49  
% 8.03/1.49  fof(f45,plain,(
% 8.03/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 8.03/1.49    inference(cnf_transformation,[],[f34])).
% 8.03/1.49  
% 8.03/1.49  fof(f73,plain,(
% 8.03/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.03/1.49    inference(equality_resolution,[],[f45])).
% 8.03/1.49  
% 8.03/1.49  fof(f49,plain,(
% 8.03/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.03/1.49    inference(cnf_transformation,[],[f35])).
% 8.03/1.49  
% 8.03/1.49  fof(f66,plain,(
% 8.03/1.49    ( ! [X0] : (v3_tdlat_3(X0) | ~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 8.03/1.49    inference(cnf_transformation,[],[f41])).
% 8.03/1.49  
% 8.03/1.49  fof(f71,plain,(
% 8.03/1.49    ~v3_tdlat_3(sK2)),
% 8.03/1.49    inference(cnf_transformation,[],[f44])).
% 8.03/1.49  
% 8.03/1.49  fof(f65,plain,(
% 8.03/1.49    ( ! [X0] : (v3_tdlat_3(X0) | r2_hidden(sK0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 8.03/1.49    inference(cnf_transformation,[],[f41])).
% 8.03/1.49  
% 8.03/1.49  fof(f64,plain,(
% 8.03/1.49    ( ! [X0] : (v3_tdlat_3(X0) | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.03/1.49    inference(cnf_transformation,[],[f41])).
% 8.03/1.49  
% 8.03/1.49  fof(f70,plain,(
% 8.03/1.49    v3_tdlat_3(sK1)),
% 8.03/1.49    inference(cnf_transformation,[],[f44])).
% 8.03/1.49  
% 8.03/1.49  cnf(c_831,plain,
% 8.03/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1468,plain,
% 8.03/1.49      ( ~ r2_hidden(X0,X1)
% 8.03/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 8.03/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
% 8.03/1.49      | u1_pre_topc(sK2) != X1 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_831]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1507,plain,
% 8.03/1.49      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 8.03/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 8.03/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
% 8.03/1.49      | u1_pre_topc(sK2) != u1_pre_topc(X1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1468]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_9625,plain,
% 8.03/1.49      ( ~ r2_hidden(k6_subset_1(X0,X1),u1_pre_topc(X2))
% 8.03/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 8.03/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
% 8.03/1.49      | u1_pre_topc(sK2) != u1_pre_topc(X2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1507]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_39605,plain,
% 8.03/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X1))
% 8.03/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 8.03/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 8.03/1.49      | u1_pre_topc(sK2) != u1_pre_topc(X1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_9625]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_39607,plain,
% 8.03/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 8.03/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 8.03/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 8.03/1.49      | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_39605]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_830,plain,
% 8.03/1.49      ( X0 != X1 | X2 != X3 | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_11664,plain,
% 8.03/1.49      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,X1)
% 8.03/1.49      | sK0(sK2) != X1
% 8.03/1.49      | u1_struct_0(sK2) != X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_830]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_17016,plain,
% 8.03/1.49      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,sK0(sK2))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | u1_struct_0(sK2) != X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_11664]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_26646,plain,
% 8.03/1.49      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_17016]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_26647,plain,
% 8.03/1.49      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_26646]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_21,plain,
% 8.03/1.49      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 8.03/1.49      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.49      | ~ v3_tdlat_3(X1)
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_22830,plain,
% 8.03/1.49      ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 8.03/1.49      | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 8.03/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 8.03/1.49      | ~ v3_tdlat_3(X0)
% 8.03/1.49      | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_22837,plain,
% 8.03/1.49      ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 8.03/1.49      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 8.03/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 8.03/1.49      | ~ v3_tdlat_3(sK1)
% 8.03/1.49      | ~ l1_pre_topc(sK1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_22830]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_9865,plain,
% 8.03/1.49      ( ~ r2_hidden(X0,X1)
% 8.03/1.49      | r2_hidden(X2,u1_pre_topc(X3))
% 8.03/1.49      | X2 != X0
% 8.03/1.49      | u1_pre_topc(X3) != X1 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_831]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_11879,plain,
% 8.03/1.49      ( r2_hidden(X0,u1_pre_topc(X1))
% 8.03/1.49      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 8.03/1.49      | X0 != sK0(sK2)
% 8.03/1.49      | u1_pre_topc(X1) != u1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_9865]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_15732,plain,
% 8.03/1.49      ( r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 8.03/1.49      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | u1_pre_topc(X0) != u1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_11879]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_15734,plain,
% 8.03/1.49      ( r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 8.03/1.49      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | u1_pre_topc(sK1) != u1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_15732]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_819,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3410,plain,
% 8.03/1.49      ( X0 != X1 | X0 = u1_pre_topc(X2) | u1_pre_topc(X2) != X1 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_819]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4402,plain,
% 8.03/1.49      ( X0 != u1_pre_topc(X1)
% 8.03/1.49      | X0 = u1_pre_topc(X2)
% 8.03/1.49      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3410]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5933,plain,
% 8.03/1.49      ( u1_pre_topc(X0) != u1_pre_topc(X0)
% 8.03/1.49      | u1_pre_topc(X1) != u1_pre_topc(X0)
% 8.03/1.49      | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4402]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8641,plain,
% 8.03/1.49      ( u1_pre_topc(X0) != u1_pre_topc(X0)
% 8.03/1.49      | u1_pre_topc(X0) = u1_pre_topc(sK2)
% 8.03/1.49      | u1_pre_topc(sK2) != u1_pre_topc(X0) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_5933]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8642,plain,
% 8.03/1.49      ( u1_pre_topc(sK1) != u1_pre_topc(sK1)
% 8.03/1.49      | u1_pre_topc(sK1) = u1_pre_topc(sK2)
% 8.03/1.49      | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_8641]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f51]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1419,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_11,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.03/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1416,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 8.03/1.49      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2761,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_1419,c_1416]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_63,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top
% 8.03/1.49      | l1_pre_topc(X0) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3510,plain,
% 8.03/1.49      ( l1_pre_topc(X1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,X1) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2761,c_63]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3511,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_3510]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_14,plain,
% 8.03/1.49      ( ~ v1_tops_2(X0,X1)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.03/1.49      | r1_tarski(X0,u1_pre_topc(X1))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f58]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1413,plain,
% 8.03/1.49      ( v1_tops_2(X0,X1) != iProver_top
% 8.03/1.49      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 8.03/1.49      | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3518,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_3511,c_1413]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_17,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1410,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X0) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_24,negated_conjecture,
% 8.03/1.49      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 8.03/1.49      inference(cnf_transformation,[],[f69]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1)
% 8.03/1.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1417,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2241,plain,
% 8.03/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK1) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_24,c_1417]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_26,negated_conjecture,
% 8.03/1.49      ( l1_pre_topc(sK1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f67]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_27,plain,
% 8.03/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2329,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK1) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2241,c_27]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2330,plain,
% 8.03/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK1) = iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_2329]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2336,plain,
% 8.03/1.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 8.03/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_1410,c_2330]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_10,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.03/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 8.03/1.49      | ~ l1_pre_topc(X0)
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_145,plain,
% 8.03/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 8.03/1.49      | ~ m1_pre_topc(X0,X1)
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_10,c_5]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_146,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.03/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_145]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1401,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2335,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK1) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_1401,c_2330]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_25,negated_conjecture,
% 8.03/1.49      ( l1_pre_topc(sK2) ),
% 8.03/1.49      inference(cnf_transformation,[],[f68]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_28,plain,
% 8.03/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2416,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK1) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2335,c_28]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2417,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK1) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_2416]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2422,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_1410,c_2417]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2576,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2422,c_28]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_16,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.03/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f61]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1411,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.03/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 8.03/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1418,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.03/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2719,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_pre_topc(X1,X2) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top
% 8.03/1.49      | l1_pre_topc(X2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_1411,c_1418]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3818,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2576,c_2719]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4468,plain,
% 8.03/1.49      ( l1_pre_topc(X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.03/1.49      | m1_pre_topc(sK1,X0) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_3818,c_27]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4469,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_4468]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4473,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_4469,c_1418]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5840,plain,
% 8.03/1.49      ( l1_pre_topc(X1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.03/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,X1) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_4473,c_63]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5841,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.03/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_5840]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5852,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 8.03/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2336,c_5841]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_37,plain,
% 8.03/1.49      ( m1_pre_topc(X0,X0) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_39,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,sK1) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_37]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3829,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,sK1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3818]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6116,plain,
% 8.03/1.49      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_5852,c_27,c_39,c_3829]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f48]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1421,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.03/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6120,plain,
% 8.03/1.49      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_6116,c_1421]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_0,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 8.03/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1424,plain,
% 8.03/1.49      ( X0 = X1
% 8.03/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.03/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6522,plain,
% 8.03/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 8.03/1.49      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_6120,c_1424]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2182,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2183,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2182]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1762,plain,
% 8.03/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_24,c_1401]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1915,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_1762,c_27]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1916,plain,
% 8.03/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK1) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_1915]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2240,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK2) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_1916,c_1417]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2343,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK2) = iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK1) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2240,c_28]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2344,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK2) = iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_2343]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2349,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,sK2) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_1410,c_2344]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2246,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,sK1) != iProver_top
% 8.03/1.49      | m1_pre_topc(sK1,sK2) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2240]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2494,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2349,c_27,c_28,c_39,c_2246]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3821,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2494,c_2719]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4479,plain,
% 8.03/1.49      ( l1_pre_topc(X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.03/1.49      | m1_pre_topc(sK2,X0) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_3821,c_28]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4480,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_4479]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4485,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,X0) != iProver_top
% 8.03/1.49      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_4480,c_1421]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4472,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,X0) != iProver_top
% 8.03/1.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_4469,c_1421]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4590,plain,
% 8.03/1.49      ( u1_struct_0(X0) = u1_struct_0(sK2)
% 8.03/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 8.03/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_4472,c_1424]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4698,plain,
% 8.03/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 8.03/1.49      | m1_pre_topc(sK1,sK1) != iProver_top
% 8.03/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_4485,c_4590]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6602,plain,
% 8.03/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_6522,c_27,c_28,c_39,c_2183,c_4698]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6653,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_6602,c_1419]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_60,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_62,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_60]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2084,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,sK2)
% 8.03/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2463,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,sK2)
% 8.03/1.49      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2084]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2464,plain,
% 8.03/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2463]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2466,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2464]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7072,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_6653,c_27,c_28,c_39,c_62,c_2246,c_2466]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7081,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK1),sK2) != iProver_top
% 8.03/1.49      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2)) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_7072,c_1413]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_15,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(X0),X0) | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f60]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_43,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_45,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_43]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_12,plain,
% 8.03/1.49      ( ~ v1_tops_2(X0,X1)
% 8.03/1.49      | v1_tops_2(X0,X2)
% 8.03/1.49      | ~ m1_pre_topc(X2,X1)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f74]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1633,plain,
% 8.03/1.49      ( ~ v1_tops_2(X0,X1)
% 8.03/1.49      | v1_tops_2(X0,sK2)
% 8.03/1.49      | ~ m1_pre_topc(sK2,X1)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2788,plain,
% 8.03/1.49      ( ~ v1_tops_2(u1_pre_topc(X0),X1)
% 8.03/1.49      | v1_tops_2(u1_pre_topc(X0),sK2)
% 8.03/1.49      | ~ m1_pre_topc(sK2,X1)
% 8.03/1.49      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.03/1.49      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(X1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1633]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2799,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
% 8.03/1.49      | v1_tops_2(u1_pre_topc(X0),sK2) = iProver_top
% 8.03/1.49      | m1_pre_topc(sK2,X1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2788]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2801,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK1),sK1) != iProver_top
% 8.03/1.49      | v1_tops_2(u1_pre_topc(sK1),sK2) = iProver_top
% 8.03/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2799]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1545,plain,
% 8.03/1.49      ( ~ v1_tops_2(X0,sK2)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | r1_tarski(X0,u1_pre_topc(sK2))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3056,plain,
% 8.03/1.49      ( ~ v1_tops_2(u1_pre_topc(X0),sK2)
% 8.03/1.49      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1545]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3057,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(X0),sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2)) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_3056]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3059,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK1),sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2)) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3057]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8459,plain,
% 8.03/1.49      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2)) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_7081,c_27,c_28,c_39,c_45,c_62,c_2246,c_2422,c_2466,
% 8.03/1.49                 c_2801,c_3059]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8463,plain,
% 8.03/1.49      ( u1_pre_topc(sK2) = u1_pre_topc(sK1)
% 8.03/1.49      | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_8459,c_1424]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8467,plain,
% 8.03/1.49      ( u1_pre_topc(sK2) = u1_pre_topc(sK1)
% 8.03/1.49      | v1_tops_2(u1_pre_topc(sK2),sK1) != iProver_top
% 8.03/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_3518,c_8463]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_822,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3107,plain,
% 8.03/1.49      ( m1_subset_1(X0,X1)
% 8.03/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | X0 != sK0(sK2)
% 8.03/1.49      | X1 != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_822]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3597,plain,
% 8.03/1.49      ( m1_subset_1(sK0(sK2),X0)
% 8.03/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | X0 != k1_zfmisc_1(u1_struct_0(sK2))
% 8.03/1.49      | sK0(sK2) != sK0(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3107]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4649,plain,
% 8.03/1.49      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(X0))
% 8.03/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3597]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7924,plain,
% 8.03/1.49      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 8.03/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4649]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7931,plain,
% 8.03/1.49      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 8.03/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | sK0(sK2) != sK0(sK2)
% 8.03/1.49      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_7924]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7468,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK2),X0)
% 8.03/1.49      | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
% 8.03/1.49      | ~ m1_pre_topc(X0,sK2)
% 8.03/1.49      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7469,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK2),X0) = iProver_top
% 8.03/1.49      | v1_tops_2(u1_pre_topc(sK2),sK2) != iProver_top
% 8.03/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_7468]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7471,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK2),sK1) = iProver_top
% 8.03/1.49      | v1_tops_2(u1_pre_topc(sK2),sK2) != iProver_top
% 8.03/1.49      | m1_pre_topc(sK1,sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_7469]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2772,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.03/1.49      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5236,plain,
% 8.03/1.49      ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2772]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5238,plain,
% 8.03/1.49      ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_5236]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3474,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.49      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(X1)),X0)
% 8.03/1.49      | k1_zfmisc_1(u1_struct_0(X1)) = X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4421,plain,
% 8.03/1.49      ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(X0)))
% 8.03/1.49      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3474]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4423,plain,
% 8.03/1.49      ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 8.03/1.49      | k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4421]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4152,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,sK2)
% 8.03/1.49      | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2084]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4154,plain,
% 8.03/1.49      ( ~ m1_pre_topc(sK1,sK2)
% 8.03/1.49      | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 8.03/1.49      | m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4152]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3392,plain,
% 8.03/1.49      ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2772]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3394,plain,
% 8.03/1.49      ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 8.03/1.49      | r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3392]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2,plain,
% 8.03/1.49      ( r1_tarski(X0,X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3363,plain,
% 8.03/1.49      ( r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3365,plain,
% 8.03/1.49      ( r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3363]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2860,plain,
% 8.03/1.49      ( ~ m1_pre_topc(sK2,X0)
% 8.03/1.49      | m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2862,plain,
% 8.03/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 8.03/1.49      | m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 8.03/1.49      | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(sK1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2860]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2844,plain,
% 8.03/1.49      ( ~ m1_pre_topc(sK2,X0)
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2845,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2844]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2847,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 8.03/1.49      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 8.03/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2845]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2458,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.03/1.49      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2777,plain,
% 8.03/1.49      ( m1_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.03/1.49      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2458]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2779,plain,
% 8.03/1.49      ( m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 8.03/1.49      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2777]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2476,plain,
% 8.03/1.49      ( r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2423,plain,
% 8.03/1.49      ( m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2422]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2078,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2271,plain,
% 8.03/1.49      ( m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2078]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2245,plain,
% 8.03/1.49      ( ~ m1_pre_topc(X0,sK1)
% 8.03/1.49      | m1_pre_topc(X0,sK2)
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2240]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2247,plain,
% 8.03/1.49      ( ~ m1_pre_topc(sK1,sK1)
% 8.03/1.49      | m1_pre_topc(sK1,sK2)
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2245]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_818,plain,( X0 = X0 ),theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2128,plain,
% 8.03/1.49      ( sK0(sK2) = sK0(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_818]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1881,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1882,plain,
% 8.03/1.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1718,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK2),sK2) | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1719,plain,
% 8.03/1.49      ( v1_tops_2(u1_pre_topc(sK2),sK2) = iProver_top
% 8.03/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_1718]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_825,plain,
% 8.03/1.49      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_837,plain,
% 8.03/1.49      ( u1_pre_topc(sK1) = u1_pre_topc(sK1) | sK1 != sK1 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_825]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_18,plain,
% 8.03/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 8.03/1.49      | v3_tdlat_3(X0)
% 8.03/1.49      | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f66]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_22,negated_conjecture,
% 8.03/1.49      ( ~ v3_tdlat_3(sK2) ),
% 8.03/1.49      inference(cnf_transformation,[],[f71]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_413,plain,
% 8.03/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 8.03/1.49      | ~ l1_pre_topc(X0)
% 8.03/1.49      | sK2 != X0 ),
% 8.03/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_414,plain,
% 8.03/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(unflattening,[status(thm)],[c_413]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_19,plain,
% 8.03/1.49      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 8.03/1.49      | v3_tdlat_3(X0)
% 8.03/1.49      | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f65]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_402,plain,
% 8.03/1.49      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 8.03/1.49      | ~ l1_pre_topc(X0)
% 8.03/1.49      | sK2 != X0 ),
% 8.03/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_403,plain,
% 8.03/1.49      ( r2_hidden(sK0(sK2),u1_pre_topc(sK2)) | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(unflattening,[status(thm)],[c_402]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_20,plain,
% 8.03/1.49      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 8.03/1.49      | v3_tdlat_3(X0)
% 8.03/1.49      | ~ l1_pre_topc(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f64]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_391,plain,
% 8.03/1.49      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 8.03/1.49      | ~ l1_pre_topc(X0)
% 8.03/1.49      | sK2 != X0 ),
% 8.03/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_392,plain,
% 8.03/1.49      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 8.03/1.49      | ~ l1_pre_topc(sK2) ),
% 8.03/1.49      inference(unflattening,[status(thm)],[c_391]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_75,plain,
% 8.03/1.49      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_71,plain,
% 8.03/1.49      ( r1_tarski(sK1,sK1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_38,plain,
% 8.03/1.49      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_23,negated_conjecture,
% 8.03/1.49      ( v3_tdlat_3(sK1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(contradiction,plain,
% 8.03/1.49      ( $false ),
% 8.03/1.49      inference(minisat,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_39607,c_26647,c_22837,c_15734,c_8642,c_8467,c_7931,
% 8.03/1.49                 c_7471,c_5238,c_4698,c_4423,c_4154,c_3394,c_3365,c_2862,
% 8.03/1.49                 c_2847,c_2779,c_2476,c_2423,c_2422,c_2271,c_2247,c_2246,
% 8.03/1.49                 c_2183,c_2128,c_1882,c_1719,c_837,c_414,c_403,c_392,
% 8.03/1.49                 c_75,c_71,c_39,c_38,c_23,c_28,c_25,c_27,c_26]) ).
% 8.03/1.49  
% 8.03/1.49  
% 8.03/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.03/1.49  
% 8.03/1.49  ------                               Statistics
% 8.03/1.49  
% 8.03/1.49  ------ General
% 8.03/1.49  
% 8.03/1.49  abstr_ref_over_cycles:                  0
% 8.03/1.49  abstr_ref_under_cycles:                 0
% 8.03/1.49  gc_basic_clause_elim:                   0
% 8.03/1.49  forced_gc_time:                         0
% 8.03/1.49  parsing_time:                           0.007
% 8.03/1.49  unif_index_cands_time:                  0.
% 8.03/1.49  unif_index_add_time:                    0.
% 8.03/1.49  orderings_time:                         0.
% 8.03/1.49  out_proof_time:                         0.014
% 8.03/1.49  total_time:                             0.945
% 8.03/1.49  num_of_symbols:                         46
% 8.03/1.49  num_of_terms:                           11580
% 8.03/1.49  
% 8.03/1.49  ------ Preprocessing
% 8.03/1.49  
% 8.03/1.49  num_of_splits:                          0
% 8.03/1.49  num_of_split_atoms:                     0
% 8.03/1.49  num_of_reused_defs:                     0
% 8.03/1.49  num_eq_ax_congr_red:                    12
% 8.03/1.49  num_of_sem_filtered_clauses:            1
% 8.03/1.49  num_of_subtypes:                        0
% 8.03/1.49  monotx_restored_types:                  0
% 8.03/1.49  sat_num_of_epr_types:                   0
% 8.03/1.49  sat_num_of_non_cyclic_types:            0
% 8.03/1.49  sat_guarded_non_collapsed_types:        0
% 8.03/1.49  num_pure_diseq_elim:                    0
% 8.03/1.49  simp_replaced_by:                       0
% 8.03/1.49  res_preprocessed:                       129
% 8.03/1.49  prep_upred:                             0
% 8.03/1.49  prep_unflattend:                        14
% 8.03/1.49  smt_new_axioms:                         0
% 8.03/1.49  pred_elim_cands:                        7
% 8.03/1.49  pred_elim:                              0
% 8.03/1.49  pred_elim_cl:                           0
% 8.03/1.49  pred_elim_cycles:                       2
% 8.03/1.49  merged_defs:                            8
% 8.03/1.49  merged_defs_ncl:                        0
% 8.03/1.49  bin_hyper_res:                          8
% 8.03/1.49  prep_cycles:                            4
% 8.03/1.49  pred_elim_time:                         0.003
% 8.03/1.49  splitting_time:                         0.
% 8.03/1.49  sem_filter_time:                        0.
% 8.03/1.49  monotx_time:                            0.
% 8.03/1.49  subtype_inf_time:                       0.
% 8.03/1.49  
% 8.03/1.49  ------ Problem properties
% 8.03/1.49  
% 8.03/1.49  clauses:                                25
% 8.03/1.49  conjectures:                            5
% 8.03/1.49  epr:                                    8
% 8.03/1.49  horn:                                   23
% 8.03/1.49  ground:                                 5
% 8.03/1.49  unary:                                  6
% 8.03/1.49  binary:                                 5
% 8.03/1.49  lits:                                   67
% 8.03/1.49  lits_eq:                                2
% 8.03/1.49  fd_pure:                                0
% 8.03/1.49  fd_pseudo:                              0
% 8.03/1.49  fd_cond:                                0
% 8.03/1.49  fd_pseudo_cond:                         1
% 8.03/1.49  ac_symbols:                             0
% 8.03/1.49  
% 8.03/1.49  ------ Propositional Solver
% 8.03/1.49  
% 8.03/1.49  prop_solver_calls:                      42
% 8.03/1.49  prop_fast_solver_calls:                 3126
% 8.03/1.49  smt_solver_calls:                       0
% 8.03/1.49  smt_fast_solver_calls:                  0
% 8.03/1.49  prop_num_of_clauses:                    9172
% 8.03/1.49  prop_preprocess_simplified:             16246
% 8.03/1.49  prop_fo_subsumed:                       286
% 8.03/1.49  prop_solver_time:                       0.
% 8.03/1.49  smt_solver_time:                        0.
% 8.03/1.49  smt_fast_solver_time:                   0.
% 8.03/1.49  prop_fast_solver_time:                  0.
% 8.03/1.49  prop_unsat_core_time:                   0.001
% 8.03/1.49  
% 8.03/1.49  ------ QBF
% 8.03/1.49  
% 8.03/1.49  qbf_q_res:                              0
% 8.03/1.49  qbf_num_tautologies:                    0
% 8.03/1.49  qbf_prep_cycles:                        0
% 8.03/1.49  
% 8.03/1.49  ------ BMC1
% 8.03/1.49  
% 8.03/1.49  bmc1_current_bound:                     -1
% 8.03/1.49  bmc1_last_solved_bound:                 -1
% 8.03/1.49  bmc1_unsat_core_size:                   -1
% 8.03/1.49  bmc1_unsat_core_parents_size:           -1
% 8.03/1.49  bmc1_merge_next_fun:                    0
% 8.03/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.03/1.49  
% 8.03/1.49  ------ Instantiation
% 8.03/1.49  
% 8.03/1.49  inst_num_of_clauses:                    2205
% 8.03/1.49  inst_num_in_passive:                    176
% 8.03/1.49  inst_num_in_active:                     1767
% 8.03/1.49  inst_num_in_unprocessed:                261
% 8.03/1.49  inst_num_of_loops:                      1868
% 8.03/1.49  inst_num_of_learning_restarts:          0
% 8.03/1.49  inst_num_moves_active_passive:          87
% 8.03/1.49  inst_lit_activity:                      0
% 8.03/1.49  inst_lit_activity_moves:                0
% 8.03/1.49  inst_num_tautologies:                   0
% 8.03/1.49  inst_num_prop_implied:                  0
% 8.03/1.49  inst_num_existing_simplified:           0
% 8.03/1.49  inst_num_eq_res_simplified:             0
% 8.03/1.49  inst_num_child_elim:                    0
% 8.03/1.49  inst_num_of_dismatching_blockings:      5349
% 8.03/1.49  inst_num_of_non_proper_insts:           9599
% 8.03/1.49  inst_num_of_duplicates:                 0
% 8.03/1.49  inst_inst_num_from_inst_to_res:         0
% 8.03/1.49  inst_dismatching_checking_time:         0.
% 8.03/1.49  
% 8.03/1.49  ------ Resolution
% 8.03/1.49  
% 8.03/1.49  res_num_of_clauses:                     0
% 8.03/1.49  res_num_in_passive:                     0
% 8.03/1.49  res_num_in_active:                      0
% 8.03/1.49  res_num_of_loops:                       133
% 8.03/1.49  res_forward_subset_subsumed:            1501
% 8.03/1.49  res_backward_subset_subsumed:           0
% 8.03/1.49  res_forward_subsumed:                   0
% 8.03/1.49  res_backward_subsumed:                  0
% 8.03/1.49  res_forward_subsumption_resolution:     0
% 8.03/1.49  res_backward_subsumption_resolution:    0
% 8.03/1.49  res_clause_to_clause_subsumption:       5137
% 8.03/1.49  res_orphan_elimination:                 0
% 8.03/1.49  res_tautology_del:                      2009
% 8.03/1.49  res_num_eq_res_simplified:              0
% 8.03/1.49  res_num_sel_changes:                    0
% 8.03/1.49  res_moves_from_active_to_pass:          0
% 8.03/1.49  
% 8.03/1.49  ------ Superposition
% 8.03/1.49  
% 8.03/1.49  sup_time_total:                         0.
% 8.03/1.49  sup_time_generating:                    0.
% 8.03/1.49  sup_time_sim_full:                      0.
% 8.03/1.49  sup_time_sim_immed:                     0.
% 8.03/1.49  
% 8.03/1.49  sup_num_of_clauses:                     983
% 8.03/1.49  sup_num_in_active:                      356
% 8.03/1.49  sup_num_in_passive:                     627
% 8.03/1.49  sup_num_of_loops:                       372
% 8.03/1.49  sup_fw_superposition:                   1177
% 8.03/1.49  sup_bw_superposition:                   960
% 8.03/1.49  sup_immediate_simplified:               618
% 8.03/1.49  sup_given_eliminated:                   1
% 8.03/1.49  comparisons_done:                       0
% 8.03/1.49  comparisons_avoided:                    0
% 8.03/1.49  
% 8.03/1.49  ------ Simplifications
% 8.03/1.49  
% 8.03/1.49  
% 8.03/1.49  sim_fw_subset_subsumed:                 143
% 8.03/1.49  sim_bw_subset_subsumed:                 53
% 8.03/1.49  sim_fw_subsumed:                        335
% 8.03/1.49  sim_bw_subsumed:                        51
% 8.03/1.49  sim_fw_subsumption_res:                 0
% 8.03/1.49  sim_bw_subsumption_res:                 0
% 8.03/1.49  sim_tautology_del:                      148
% 8.03/1.49  sim_eq_tautology_del:                   37
% 8.03/1.49  sim_eq_res_simp:                        0
% 8.03/1.49  sim_fw_demodulated:                     8
% 8.03/1.49  sim_bw_demodulated:                     11
% 8.03/1.49  sim_light_normalised:                   183
% 8.03/1.49  sim_joinable_taut:                      0
% 8.03/1.49  sim_joinable_simp:                      0
% 8.03/1.49  sim_ac_normalised:                      0
% 8.03/1.49  sim_smt_subsumption:                    0
% 8.03/1.49  
%------------------------------------------------------------------------------
