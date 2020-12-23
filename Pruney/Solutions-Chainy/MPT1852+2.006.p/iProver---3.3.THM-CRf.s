%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:34 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 585 expanded)
%              Number of clauses        :  140 ( 234 expanded)
%              Number of leaves         :   22 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          :  681 (2361 expanded)
%              Number of equality atoms :  201 ( 519 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
    ( ~ v3_tdlat_3(sK2)
    & v3_tdlat_3(sK1)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f37,f36])).

fof(f59,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
        & r2_hidden(sK0(X0),u1_pre_topc(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f53,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | r2_hidden(sK0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f60,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_657,plain,
    ( X0 != X1
    | X2 != X3
    | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_6490,plain,
    ( X0 != sK0(sK2)
    | X1 != u1_struct_0(X2)
    | k6_subset_1(X1,X0) = k6_subset_1(u1_struct_0(X2),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_6535,plain,
    ( X0 != u1_struct_0(X1)
    | k6_subset_1(X0,sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
    | sK0(sK2) != sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_6490])).

cnf(c_6587,plain,
    ( k6_subset_1(u1_struct_0(X0),sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(X0) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_6535])).

cnf(c_7203,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6587])).

cnf(c_7204,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7203])).

cnf(c_658,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5616,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
    | X0 != k6_subset_1(u1_struct_0(X2),sK0(sK2))
    | X1 != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_6228,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
    | X0 != k6_subset_1(u1_struct_0(X2),sK0(sK2))
    | u1_pre_topc(X1) != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_5616])).

cnf(c_6489,plain,
    ( r2_hidden(k6_subset_1(X0,X1),u1_pre_topc(X2))
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X3),sK0(sK2)),u1_pre_topc(X3))
    | k6_subset_1(X0,X1) != k6_subset_1(u1_struct_0(X3),sK0(sK2))
    | u1_pre_topc(X2) != u1_pre_topc(X3) ),
    inference(instantiation,[status(thm)],[c_6228])).

cnf(c_6571,plain,
    ( r2_hidden(k6_subset_1(X0,sK0(sK2)),u1_pre_topc(X1))
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
    | k6_subset_1(X0,sK0(sK2)) != k6_subset_1(u1_struct_0(X2),sK0(sK2))
    | u1_pre_topc(X1) != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_6489])).

cnf(c_6765,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),sK0(sK2)),u1_pre_topc(X2))
    | k6_subset_1(u1_struct_0(X1),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_pre_topc(X2) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6571])).

cnf(c_7027,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_pre_topc(sK2) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6765])).

cnf(c_7029,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_7027])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1235,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5087,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_5089,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5087])).

cnf(c_9,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1293,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4757,plain,
    ( v1_tops_2(u1_pre_topc(sK2),X0)
    | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_4759,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK1)
    | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4757])).

cnf(c_11,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1535,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4178,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK2),X0)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_4180,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK2),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4178])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3444,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3419,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_3421,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3419])).

cnf(c_10,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1668,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2797,plain,
    ( v1_tops_2(u1_pre_topc(X0),sK2)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_3336,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2797])).

cnf(c_647,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1938,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_2236,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_2578,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_3233,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_3234,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3233])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1044,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_122,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_3])).

cnf(c_123,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_122])).

cnf(c_1034,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123])).

cnf(c_1363,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1034])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1517,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_23])).

cnf(c_1518,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1517])).

cnf(c_5,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1049,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1689,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1049])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1794,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1689,c_24])).

cnf(c_1795,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1794])).

cnf(c_1802,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1795])).

cnf(c_36,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_38,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1713,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_2045,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1802,c_23,c_24,c_38,c_1713])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1043,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1053,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1595,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_1053])).

cnf(c_2586,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_1595])).

cnf(c_55,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3039,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2586,c_55])).

cnf(c_3040,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3039])).

cnf(c_3052,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_3040])).

cnf(c_2798,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),X0)
    | v1_tops_2(u1_pre_topc(X0),sK2)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_2800,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | v1_tops_2(u1_pre_topc(sK1),sK2)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2798])).

cnf(c_2329,plain,
    ( ~ v1_tops_2(u1_pre_topc(X0),sK2)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_2331,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK2)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2329])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1238,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2324,plain,
    ( r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1268,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != sK0(sK2)
    | X1 != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_1414,plain,
    ( m1_subset_1(sK0(sK2),X0)
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK2))
    | sK0(sK2) != sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1867,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2) != sK0(sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_2310,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2) != sK0(sK2)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_2312,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2) != sK0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_1311,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ r1_tarski(u1_pre_topc(X1),X0)
    | X0 = u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1666,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
    | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
    | u1_pre_topc(X1) = u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_2116,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
    | u1_pre_topc(sK2) = u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_2118,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    | u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_2111,plain,
    ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
    | u1_pre_topc(X0) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_2113,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
    | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    | u1_pre_topc(sK1) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_1690,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1049])).

cnf(c_1768,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1690,c_23])).

cnf(c_1769,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1768])).

cnf(c_1776,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1769])).

cnf(c_2052,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1776,c_24])).

cnf(c_2053,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2052])).

cnf(c_2060,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_2053])).

cnf(c_2068,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2060])).

cnf(c_653,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1661,plain,
    ( X0 != u1_struct_0(X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_1866,plain,
    ( X0 != u1_struct_0(sK2)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_1954,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_1956,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_1712,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1689])).

cnf(c_1714,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1712])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1553,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1555,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_1263,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | X0 != sK0(sK2)
    | X1 != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1341,plain,
    ( r2_hidden(sK0(sK2),X0)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | X0 != u1_pre_topc(sK2)
    | sK0(sK2) != sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1435,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_pre_topc(X0) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_1438,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_pre_topc(sK1) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_646,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1342,plain,
    ( sK0(sK2) = sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_1239,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1245,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_1241,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_652,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_663,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_14,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_318,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_319,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_15,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_307,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_308,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_16,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_296,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_297,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_61,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_57,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_53,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_37,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_19,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7204,c_7029,c_5089,c_4759,c_4180,c_3444,c_3421,c_3336,c_3234,c_3052,c_2800,c_2331,c_2324,c_2312,c_2118,c_2113,c_2068,c_2060,c_1956,c_1714,c_1555,c_1438,c_1342,c_1245,c_1241,c_663,c_319,c_308,c_297,c_61,c_57,c_53,c_37,c_19,c_24,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.18/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.99  
% 3.18/0.99  ------  iProver source info
% 3.18/0.99  
% 3.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.99  git: non_committed_changes: false
% 3.18/0.99  git: last_make_outside_of_git: false
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     num_symb
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       true
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  ------ Parsing...
% 3.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.99  ------ Proving...
% 3.18/0.99  ------ Problem Properties 
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  clauses                                 21
% 3.18/0.99  conjectures                             5
% 3.18/0.99  EPR                                     8
% 3.18/0.99  Horn                                    19
% 3.18/0.99  unary                                   6
% 3.18/0.99  binary                                  2
% 3.18/0.99  lits                                    57
% 3.18/0.99  lits eq                                 2
% 3.18/0.99  fd_pure                                 0
% 3.18/0.99  fd_pseudo                               0
% 3.18/0.99  fd_cond                                 0
% 3.18/0.99  fd_pseudo_cond                          1
% 3.18/0.99  AC symbols                              0
% 3.18/0.99  
% 3.18/0.99  ------ Schedule dynamic 5 is on 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  Current options:
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     none
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       false
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ Proving...
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS status Theorem for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  fof(f6,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f18,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f6])).
% 3.18/0.99  
% 3.18/0.99  fof(f47,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f18])).
% 3.18/0.99  
% 3.18/0.99  fof(f7,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f19,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f7])).
% 3.18/0.99  
% 3.18/0.99  fof(f20,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f19])).
% 3.18/0.99  
% 3.18/0.99  fof(f48,plain,(
% 3.18/0.99    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f20])).
% 3.18/0.99  
% 3.18/0.99  fof(f64,plain,(
% 3.18/0.99    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(equality_resolution,[],[f48])).
% 3.18/0.99  
% 3.18/0.99  fof(f8,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f21,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f8])).
% 3.18/0.99  
% 3.18/0.99  fof(f31,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f21])).
% 3.18/0.99  
% 3.18/0.99  fof(f49,plain,(
% 3.18/0.99    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f31])).
% 3.18/0.99  
% 3.18/0.99  fof(f3,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f15,plain,(
% 3.18/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f3])).
% 3.18/0.99  
% 3.18/0.99  fof(f43,plain,(
% 3.18/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f15])).
% 3.18/0.99  
% 3.18/0.99  fof(f50,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f31])).
% 3.18/0.99  
% 3.18/0.99  fof(f9,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f22,plain,(
% 3.18/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f9])).
% 3.18/0.99  
% 3.18/0.99  fof(f51,plain,(
% 3.18/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f22])).
% 3.18/0.99  
% 3.18/0.99  fof(f12,conjecture,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f13,negated_conjecture,(
% 3.18/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 3.18/0.99    inference(negated_conjecture,[],[f12])).
% 3.18/0.99  
% 3.18/0.99  fof(f26,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f13])).
% 3.18/0.99  
% 3.18/0.99  fof(f27,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f26])).
% 3.18/0.99  
% 3.18/0.99  fof(f37,plain,(
% 3.18/0.99    ( ! [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK2) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK2))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f36,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK1))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f38,plain,(
% 3.18/0.99    (~v3_tdlat_3(sK2) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2)) & l1_pre_topc(sK1)),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f37,f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f59,plain,(
% 3.18/0.99    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.18/0.99    inference(cnf_transformation,[],[f38])).
% 3.18/0.99  
% 3.18/0.99  fof(f5,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f17,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f5])).
% 3.18/0.99  
% 3.18/0.99  fof(f30,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f17])).
% 3.18/0.99  
% 3.18/0.99  fof(f45,plain,(
% 3.18/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f30])).
% 3.18/0.99  
% 3.18/0.99  fof(f2,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f14,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f2])).
% 3.18/0.99  
% 3.18/0.99  fof(f42,plain,(
% 3.18/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f14])).
% 3.18/0.99  
% 3.18/0.99  fof(f57,plain,(
% 3.18/0.99    l1_pre_topc(sK1)),
% 3.18/0.99    inference(cnf_transformation,[],[f38])).
% 3.18/0.99  
% 3.18/0.99  fof(f4,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f16,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f4])).
% 3.18/0.99  
% 3.18/0.99  fof(f44,plain,(
% 3.18/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f16])).
% 3.18/0.99  
% 3.18/0.99  fof(f58,plain,(
% 3.18/0.99    l1_pre_topc(sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f38])).
% 3.18/0.99  
% 3.18/0.99  fof(f10,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f23,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f10])).
% 3.18/0.99  
% 3.18/0.99  fof(f52,plain,(
% 3.18/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f23])).
% 3.18/0.99  
% 3.18/0.99  fof(f1,axiom,(
% 3.18/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f28,plain,(
% 3.18/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.18/0.99    inference(nnf_transformation,[],[f1])).
% 3.18/0.99  
% 3.18/0.99  fof(f29,plain,(
% 3.18/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.18/0.99    inference(flattening,[],[f28])).
% 3.18/0.99  
% 3.18/0.99  fof(f41,plain,(
% 3.18/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f29])).
% 3.18/0.99  
% 3.18/0.99  fof(f40,plain,(
% 3.18/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.18/0.99    inference(cnf_transformation,[],[f29])).
% 3.18/0.99  
% 3.18/0.99  fof(f62,plain,(
% 3.18/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.18/0.99    inference(equality_resolution,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f11,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f24,plain,(
% 3.18/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f11])).
% 3.18/0.99  
% 3.18/0.99  fof(f25,plain,(
% 3.18/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f24])).
% 3.18/0.99  
% 3.18/0.99  fof(f32,plain,(
% 3.18/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f25])).
% 3.18/0.99  
% 3.18/0.99  fof(f33,plain,(
% 3.18/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(rectify,[],[f32])).
% 3.18/0.99  
% 3.18/0.99  fof(f34,plain,(
% 3.18/0.99    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f35,plain,(
% 3.18/0.99    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.18/0.99  
% 3.18/0.99  fof(f53,plain,(
% 3.18/0.99    ( ! [X2,X0] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f56,plain,(
% 3.18/0.99    ( ! [X0] : (v3_tdlat_3(X0) | ~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f61,plain,(
% 3.18/0.99    ~v3_tdlat_3(sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f38])).
% 3.18/0.99  
% 3.18/0.99  fof(f55,plain,(
% 3.18/0.99    ( ! [X0] : (v3_tdlat_3(X0) | r2_hidden(sK0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f54,plain,(
% 3.18/0.99    ( ! [X0] : (v3_tdlat_3(X0) | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f39,plain,(
% 3.18/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.18/0.99    inference(cnf_transformation,[],[f29])).
% 3.18/0.99  
% 3.18/0.99  fof(f63,plain,(
% 3.18/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.18/0.99    inference(equality_resolution,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f60,plain,(
% 3.18/0.99    v3_tdlat_3(sK1)),
% 3.18/0.99    inference(cnf_transformation,[],[f38])).
% 3.18/0.99  
% 3.18/0.99  cnf(c_657,plain,
% 3.18/0.99      ( X0 != X1 | X2 != X3 | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
% 3.18/0.99      theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6490,plain,
% 3.18/0.99      ( X0 != sK0(sK2)
% 3.18/0.99      | X1 != u1_struct_0(X2)
% 3.18/0.99      | k6_subset_1(X1,X0) = k6_subset_1(u1_struct_0(X2),sK0(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_657]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6535,plain,
% 3.18/0.99      ( X0 != u1_struct_0(X1)
% 3.18/0.99      | k6_subset_1(X0,sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
% 3.18/0.99      | sK0(sK2) != sK0(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6490]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6587,plain,
% 3.18/0.99      ( k6_subset_1(u1_struct_0(X0),sK0(sK2)) = k6_subset_1(u1_struct_0(X1),sK0(sK2))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | u1_struct_0(X0) != u1_struct_0(X1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6535]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7203,plain,
% 3.18/0.99      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6587]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7204,plain,
% 3.18/0.99      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_7203]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_658,plain,
% 3.18/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.18/0.99      theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5616,plain,
% 3.18/0.99      ( r2_hidden(X0,X1)
% 3.18/0.99      | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
% 3.18/0.99      | X0 != k6_subset_1(u1_struct_0(X2),sK0(sK2))
% 3.18/0.99      | X1 != u1_pre_topc(X2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6228,plain,
% 3.18/0.99      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.18/0.99      | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
% 3.18/0.99      | X0 != k6_subset_1(u1_struct_0(X2),sK0(sK2))
% 3.18/0.99      | u1_pre_topc(X1) != u1_pre_topc(X2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_5616]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6489,plain,
% 3.18/0.99      ( r2_hidden(k6_subset_1(X0,X1),u1_pre_topc(X2))
% 3.18/0.99      | ~ r2_hidden(k6_subset_1(u1_struct_0(X3),sK0(sK2)),u1_pre_topc(X3))
% 3.18/0.99      | k6_subset_1(X0,X1) != k6_subset_1(u1_struct_0(X3),sK0(sK2))
% 3.18/0.99      | u1_pre_topc(X2) != u1_pre_topc(X3) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6228]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6571,plain,
% 3.18/0.99      ( r2_hidden(k6_subset_1(X0,sK0(sK2)),u1_pre_topc(X1))
% 3.18/0.99      | ~ r2_hidden(k6_subset_1(u1_struct_0(X2),sK0(sK2)),u1_pre_topc(X2))
% 3.18/0.99      | k6_subset_1(X0,sK0(sK2)) != k6_subset_1(u1_struct_0(X2),sK0(sK2))
% 3.18/0.99      | u1_pre_topc(X1) != u1_pre_topc(X2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6489]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6765,plain,
% 3.18/0.99      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 3.18/0.99      | r2_hidden(k6_subset_1(u1_struct_0(X1),sK0(sK2)),u1_pre_topc(X2))
% 3.18/0.99      | k6_subset_1(u1_struct_0(X1),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 3.18/0.99      | u1_pre_topc(X2) != u1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6571]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7027,plain,
% 3.18/0.99      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 3.18/0.99      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 3.18/0.99      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 3.18/0.99      | u1_pre_topc(sK2) != u1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6765]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7029,plain,
% 3.18/0.99      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 3.18/0.99      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 3.18/0.99      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 3.18/0.99      | u1_pre_topc(sK2) != u1_pre_topc(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_7027]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_8,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 3.18/0.99      | ~ m1_pre_topc(X1,X2)
% 3.18/0.99      | ~ l1_pre_topc(X2) ),
% 3.18/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1235,plain,
% 3.18/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5087,plain,
% 3.18/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(sK2,X0)
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1235]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5089,plain,
% 3.18/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(sK2,sK1)
% 3.18/0.99      | ~ l1_pre_topc(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_5087]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_9,plain,
% 3.18/0.99      ( ~ v1_tops_2(X0,X1)
% 3.18/0.99      | v1_tops_2(X0,X2)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | ~ m1_pre_topc(X2,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1293,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 3.18/0.99      | v1_tops_2(u1_pre_topc(X0),X1)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | ~ m1_pre_topc(X1,X0)
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4757,plain,
% 3.18/0.99      ( v1_tops_2(u1_pre_topc(sK2),X0)
% 3.18/0.99      | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1293]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4759,plain,
% 3.18/0.99      ( v1_tops_2(u1_pre_topc(sK2),sK1)
% 3.18/0.99      | ~ v1_tops_2(u1_pre_topc(sK2),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(sK1,sK2)
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_4757]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_11,plain,
% 3.18/0.99      ( ~ v1_tops_2(X0,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | r1_tarski(X0,u1_pre_topc(X1))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1535,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),X1)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4178,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(sK2),X0)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1535]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4180,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(sK2),sK1)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.18/0.99      | r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
% 3.18/0.99      | ~ l1_pre_topc(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_4178]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4,plain,
% 3.18/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3444,plain,
% 3.18/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3419,plain,
% 3.18/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1235]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3421,plain,
% 3.18/0.99      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.18/0.99      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(sK1,sK2)
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_3419]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_10,plain,
% 3.18/0.99      ( v1_tops_2(X0,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1668,plain,
% 3.18/0.99      ( v1_tops_2(u1_pre_topc(X0),X1)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2797,plain,
% 3.18/0.99      ( v1_tops_2(u1_pre_topc(X0),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1668]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3336,plain,
% 3.18/0.99      ( v1_tops_2(u1_pre_topc(sK2),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2))
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2797]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_647,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1938,plain,
% 3.18/0.99      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_647]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2236,plain,
% 3.18/0.99      ( X0 != u1_struct_0(X1)
% 3.18/0.99      | X0 = u1_struct_0(X2)
% 3.18/0.99      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1938]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2578,plain,
% 3.18/0.99      ( u1_struct_0(X0) != u1_struct_0(X1)
% 3.18/0.99      | u1_struct_0(X2) != u1_struct_0(X1)
% 3.18/0.99      | u1_struct_0(X0) = u1_struct_0(X2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2236]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3233,plain,
% 3.18/0.99      ( u1_struct_0(X0) != u1_struct_0(X1)
% 3.18/0.99      | u1_struct_0(X0) = u1_struct_0(sK2)
% 3.18/0.99      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2578]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3234,plain,
% 3.18/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.18/0.99      | u1_struct_0(sK1) = u1_struct_0(sK2)
% 3.18/0.99      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_3233]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_12,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1044,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.18/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_20,negated_conjecture,
% 3.18/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X0)
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_122,plain,
% 3.18/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7,c_3]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_123,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_122]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1034,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_123]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1363,plain,
% 3.18/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_20,c_1034]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_22,negated_conjecture,
% 3.18/0.99      ( l1_pre_topc(sK1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_23,plain,
% 3.18/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1517,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1363,c_23]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1518,plain,
% 3.18/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_1517]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1049,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1689,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK2) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1518,c_1049]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_21,negated_conjecture,
% 3.18/0.99      ( l1_pre_topc(sK2) ),
% 3.18/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_24,plain,
% 3.18/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1794,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1689,c_24]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1795,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_1794]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1802,plain,
% 3.18/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1044,c_1795]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_36,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.18/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_38,plain,
% 3.18/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1713,plain,
% 3.18/0.99      ( m1_pre_topc(sK1,sK1) != iProver_top
% 3.18/0.99      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1689]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2045,plain,
% 3.18/0.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1802,c_23,c_24,c_38,c_1713]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_13,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1043,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_0,plain,
% 3.18/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.18/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1053,plain,
% 3.18/0.99      ( X0 = X1
% 3.18/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.18/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1595,plain,
% 3.18/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.18/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.18/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.18/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1043,c_1053]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2586,plain,
% 3.18/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.18/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | l1_pre_topc(X0) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1043,c_1595]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_55,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top
% 3.18/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3039,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.18/0.99      | u1_struct_0(X0) = u1_struct_0(X1)
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2586,c_55]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3040,plain,
% 3.18/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.18/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_3039]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3052,plain,
% 3.18/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.18/0.99      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_2045,c_3040]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2798,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),X0)
% 3.18/0.99      | v1_tops_2(u1_pre_topc(X0),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(sK2,X0)
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1293]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2800,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(sK1),sK1)
% 3.18/0.99      | v1_tops_2(u1_pre_topc(sK1),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | ~ m1_pre_topc(sK2,sK1)
% 3.18/0.99      | ~ l1_pre_topc(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2798]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2329,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(X0),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1535]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2331,plain,
% 3.18/0.99      ( ~ v1_tops_2(u1_pre_topc(sK1),sK2)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.18/0.99      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2329]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1,plain,
% 3.18/0.99      ( r1_tarski(X0,X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1238,plain,
% 3.18/0.99      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2324,plain,
% 3.18/0.99      ( r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1238]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_654,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.18/0.99      theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1268,plain,
% 3.18/0.99      ( m1_subset_1(X0,X1)
% 3.18/0.99      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.99      | X0 != sK0(sK2)
% 3.18/0.99      | X1 != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_654]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1414,plain,
% 3.18/0.99      ( m1_subset_1(sK0(sK2),X0)
% 3.18/0.99      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.99      | X0 != k1_zfmisc_1(u1_struct_0(sK2))
% 3.18/0.99      | sK0(sK2) != sK0(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1268]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1867,plain,
% 3.18/0.99      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(X0))
% 3.18/0.99      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1414]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2310,plain,
% 3.18/0.99      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/0.99      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1867]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2312,plain,
% 3.18/0.99      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.18/0.99      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2310]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1311,plain,
% 3.18/0.99      ( ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(X1),X0)
% 3.18/0.99      | X0 = u1_pre_topc(X1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1666,plain,
% 3.18/0.99      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
% 3.18/0.99      | u1_pre_topc(X1) = u1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1311]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2116,plain,
% 3.18/0.99      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
% 3.18/0.99      | u1_pre_topc(sK2) = u1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1666]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2118,plain,
% 3.18/0.99      ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
% 3.18/0.99      | u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2116]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2111,plain,
% 3.18/0.99      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(sK2))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
% 3.18/0.99      | u1_pre_topc(X0) = u1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1666]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2113,plain,
% 3.18/0.99      ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK2))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
% 3.18/0.99      | u1_pre_topc(sK1) = u1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2111]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1690,plain,
% 3.18/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK1) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_20,c_1049]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1768,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1690,c_23]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1769,plain,
% 3.18/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK1) = iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_1768]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1776,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1034,c_1769]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2052,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK1) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1776,c_24]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2053,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_2052]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2060,plain,
% 3.18/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1044,c_2053]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2068,plain,
% 3.18/0.99      ( m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2060]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_653,plain,
% 3.18/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.18/0.99      theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1661,plain,
% 3.18/0.99      ( X0 != u1_struct_0(X1)
% 3.18/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_653]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1866,plain,
% 3.18/0.99      ( X0 != u1_struct_0(sK2)
% 3.18/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1661]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1954,plain,
% 3.18/0.99      ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK2))
% 3.18/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1866]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1956,plain,
% 3.18/0.99      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK2))
% 3.18/0.99      | u1_struct_0(sK1) != u1_struct_0(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1954]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1712,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,sK1)
% 3.18/0.99      | m1_pre_topc(X0,sK2)
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1689]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1714,plain,
% 3.18/0.99      ( ~ m1_pre_topc(sK1,sK1)
% 3.18/0.99      | m1_pre_topc(sK1,sK2)
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1712]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_17,plain,
% 3.18/0.99      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.18/0.99      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.99      | ~ v3_tdlat_3(X1)
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1553,plain,
% 3.18/0.99      ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 3.18/0.99      | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 3.18/0.99      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/0.99      | ~ v3_tdlat_3(X0)
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1555,plain,
% 3.18/0.99      ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 3.18/0.99      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 3.18/0.99      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.18/0.99      | ~ v3_tdlat_3(sK1)
% 3.18/0.99      | ~ l1_pre_topc(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1553]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1263,plain,
% 3.18/0.99      ( r2_hidden(X0,X1)
% 3.18/0.99      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 3.18/0.99      | X0 != sK0(sK2)
% 3.18/0.99      | X1 != u1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1341,plain,
% 3.18/0.99      ( r2_hidden(sK0(sK2),X0)
% 3.18/0.99      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 3.18/0.99      | X0 != u1_pre_topc(sK2)
% 3.18/0.99      | sK0(sK2) != sK0(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1263]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1435,plain,
% 3.18/0.99      ( r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 3.18/0.99      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1341]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1438,plain,
% 3.18/0.99      ( r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 3.18/0.99      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 3.18/0.99      | sK0(sK2) != sK0(sK2)
% 3.18/0.99      | u1_pre_topc(sK1) != u1_pre_topc(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1435]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_646,plain,( X0 = X0 ),theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1342,plain,
% 3.18/0.99      ( sK0(sK2) = sK0(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_646]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1239,plain,
% 3.18/0.99      ( v1_tops_2(u1_pre_topc(X0),X0)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1245,plain,
% 3.18/0.99      ( v1_tops_2(u1_pre_topc(sK1),sK1)
% 3.18/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.18/0.99      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
% 3.18/0.99      | ~ l1_pre_topc(sK1) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1239]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1241,plain,
% 3.18/0.99      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1238]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_652,plain,
% 3.18/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.18/0.99      theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_663,plain,
% 3.18/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_652]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_14,plain,
% 3.18/0.99      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 3.18/0.99      | v3_tdlat_3(X0)
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_18,negated_conjecture,
% 3.18/0.99      ( ~ v3_tdlat_3(sK2) ),
% 3.18/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_318,plain,
% 3.18/0.99      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 3.18/0.99      | ~ l1_pre_topc(X0)
% 3.18/0.99      | sK2 != X0 ),
% 3.18/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_319,plain,
% 3.18/0.99      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 3.18/0.99      | ~ l1_pre_topc(sK2) ),
% 3.18/0.99      inference(unflattening,[status(thm)],[c_318]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_15,plain,
% 3.18/0.99      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 3.18/0.99      | v3_tdlat_3(X0)
% 3.18/0.99      | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_307,plain,
% 3.18/1.00      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 3.18/1.00      | ~ l1_pre_topc(X0)
% 3.18/1.00      | sK2 != X0 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_308,plain,
% 3.18/1.00      ( r2_hidden(sK0(sK2),u1_pre_topc(sK2)) | ~ l1_pre_topc(sK2) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_307]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_16,plain,
% 3.18/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/1.00      | v3_tdlat_3(X0)
% 3.18/1.00      | ~ l1_pre_topc(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_296,plain,
% 3.18/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/1.00      | ~ l1_pre_topc(X0)
% 3.18/1.00      | sK2 != X0 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_297,plain,
% 3.18/1.00      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/1.00      | ~ l1_pre_topc(sK2) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_296]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_61,plain,
% 3.18/1.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2,plain,
% 3.18/1.00      ( r1_tarski(X0,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_57,plain,
% 3.18/1.00      ( r1_tarski(sK1,sK1) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_53,plain,
% 3.18/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.18/1.00      | ~ l1_pre_topc(sK1) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_37,plain,
% 3.18/1.00      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_19,negated_conjecture,
% 3.18/1.00      ( v3_tdlat_3(sK1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_7204,c_7029,c_5089,c_4759,c_4180,c_3444,c_3421,c_3336,
% 3.18/1.00                 c_3234,c_3052,c_2800,c_2331,c_2324,c_2312,c_2118,c_2113,
% 3.18/1.00                 c_2068,c_2060,c_1956,c_1714,c_1555,c_1438,c_1342,c_1245,
% 3.18/1.00                 c_1241,c_663,c_319,c_308,c_297,c_61,c_57,c_53,c_37,c_19,
% 3.18/1.00                 c_24,c_21,c_22]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.011
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.011
% 3.18/1.00  total_time:                             0.212
% 3.18/1.00  num_of_symbols:                         46
% 3.18/1.00  num_of_terms:                           2958
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    12
% 3.18/1.00  num_of_sem_filtered_clauses:            1
% 3.18/1.00  num_of_subtypes:                        0
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        0
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       111
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        14
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        7
% 3.18/1.00  pred_elim:                              0
% 3.18/1.00  pred_elim_cl:                           0
% 3.18/1.00  pred_elim_cycles:                       2
% 3.18/1.00  merged_defs:                            0
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          0
% 3.18/1.00  prep_cycles:                            4
% 3.18/1.00  pred_elim_time:                         0.004
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.001
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                21
% 3.18/1.00  conjectures:                            5
% 3.18/1.00  epr:                                    8
% 3.18/1.00  horn:                                   19
% 3.18/1.00  ground:                                 5
% 3.18/1.00  unary:                                  6
% 3.18/1.00  binary:                                 2
% 3.18/1.00  lits:                                   57
% 3.18/1.00  lits_eq:                                2
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                0
% 3.18/1.00  fd_pseudo_cond:                         1
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      40
% 3.18/1.00  prop_fast_solver_calls:                 1101
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    1447
% 3.18/1.00  prop_preprocess_simplified:             4875
% 3.18/1.00  prop_fo_subsumed:                       49
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    375
% 3.18/1.00  inst_num_in_passive:                    9
% 3.18/1.00  inst_num_in_active:                     364
% 3.18/1.00  inst_num_in_unprocessed:                1
% 3.18/1.00  inst_num_of_loops:                      428
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          45
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                0
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      577
% 3.18/1.00  inst_num_of_non_proper_insts:           1254
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       115
% 3.18/1.00  res_forward_subset_subsumed:            135
% 3.18/1.00  res_backward_subset_subsumed:           2
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     0
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       884
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      179
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     154
% 3.18/1.00  sup_num_in_active:                      84
% 3.18/1.00  sup_num_in_passive:                     70
% 3.18/1.00  sup_num_of_loops:                       84
% 3.18/1.00  sup_fw_superposition:                   135
% 3.18/1.00  sup_bw_superposition:                   100
% 3.18/1.00  sup_immediate_simplified:               48
% 3.18/1.00  sup_given_eliminated:                   0
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    0
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 9
% 3.18/1.00  sim_bw_subset_subsumed:                 0
% 3.18/1.00  sim_fw_subsumed:                        34
% 3.18/1.00  sim_bw_subsumed:                        3
% 3.18/1.00  sim_fw_subsumption_res:                 8
% 3.18/1.00  sim_bw_subsumption_res:                 0
% 3.18/1.00  sim_tautology_del:                      20
% 3.18/1.00  sim_eq_tautology_del:                   11
% 3.18/1.00  sim_eq_res_simp:                        0
% 3.18/1.00  sim_fw_demodulated:                     0
% 3.18/1.00  sim_bw_demodulated:                     0
% 3.18/1.00  sim_light_normalised:                   10
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------
