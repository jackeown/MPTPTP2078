%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:31 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  230 (1267 expanded)
%              Number of clauses        :  158 ( 482 expanded)
%              Number of leaves         :   22 ( 269 expanded)
%              Depth                    :   30
%              Number of atoms          :  766 (4890 expanded)
%              Number of equality atoms :  290 (1177 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v2_tdlat_3(sK1)
        & v2_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ v2_tdlat_3(sK1)
    & v2_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f46,f45])).

fof(f73,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) )
        & ( k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0)
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f70,f51])).

fof(f69,plain,(
    ! [X0] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X0] :
      ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f69,f51])).

cnf(c_11,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1631,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(X0,sK0)
    | ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_16877,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1670,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_16843,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_6,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1008,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1006,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2968,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1008,c_1006])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_69,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5677,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2968,c_69])).

cnf(c_5678,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5677])).

cnf(c_13,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1003,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5688,plain,
    ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5678,c_1003])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1001,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_248,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_249,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_990,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1007,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2228,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1007])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2528,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2228,c_27])).

cnf(c_2529,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2528])).

cnf(c_2536,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_2529])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5499,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2536,c_28])).

cnf(c_5500,plain,
    ( m1_pre_topc(X0,sK0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5499])).

cnf(c_5508,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_5500])).

cnf(c_5522,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5508,c_28])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_999,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5530,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5522,c_999])).

cnf(c_23,negated_conjecture,
    ( v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,plain,
    ( v2_tdlat_3(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1233,plain,
    ( ~ v2_tdlat_3(sK0)
    | v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1234,plain,
    ( v2_tdlat_3(sK0) != iProver_top
    | v2_pre_topc(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_8576,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5530,c_27,c_29,c_1234])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1013,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8585,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8576,c_1013])).

cnf(c_1241,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_990])).

cnf(c_2259,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1241,c_27])).

cnf(c_2260,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2259])).

cnf(c_2268,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2260,c_1007])).

cnf(c_1422,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_7713,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_7717,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7713])).

cnf(c_8605,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8585,c_27,c_28,c_29,c_1234,c_2268,c_5508,c_7717])).

cnf(c_8606,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8605])).

cnf(c_8615,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_8606])).

cnf(c_3289,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2268,c_28])).

cnf(c_3290,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3289])).

cnf(c_3298,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_3290])).

cnf(c_3392,plain,
    ( m1_pre_topc(sK0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3298,c_27])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1000,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2012,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_1013])).

cnf(c_3418,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_2012])).

cnf(c_44,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7779,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_44,c_69,c_2012])).

cnf(c_7780,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7779])).

cnf(c_7796,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3392,c_7780])).

cnf(c_9518,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8615,c_28,c_5508,c_7796])).

cnf(c_9566,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9518,c_1008])).

cnf(c_1224,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1225,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1224])).

cnf(c_1227,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1228,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_1230,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1231,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_452,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1367,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[status(thm)],[c_452,c_24])).

cnf(c_1368,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1367])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1390,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1395,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1390])).

cnf(c_1406,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_1414,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_1588,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1589,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_1436,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | X0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1717,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1718,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1611,plain,
    ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2473,plain,
    ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1611])).

cnf(c_2474,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2473])).

cnf(c_453,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1583,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | X0 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_2691,plain,
    ( m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | X0 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_5207,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2691])).

cnf(c_5208,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | sK1 != sK1
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5207])).

cnf(c_6751,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8054,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6751])).

cnf(c_8055,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8054])).

cnf(c_10102,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9566,c_27,c_28,c_24,c_1225,c_1228,c_1231,c_1368,c_1395,c_1414,c_1589,c_1717,c_1718,c_2474,c_5208,c_8055])).

cnf(c_10111,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1) != iProver_top
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10102,c_1003])).

cnf(c_1389,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_1397,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_1407,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1412,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) = iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1407])).

cnf(c_12,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1305,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1493,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1494,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0) = iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_1304,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1554,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1555,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1554])).

cnf(c_1691,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(X0,sK0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2865,plain,
    ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_2866,plain,
    ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v1_tops_2(u1_pre_topc(sK0),sK0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_1557,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_2682,plain,
    ( m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X0 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_5199,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2682])).

cnf(c_5200,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | sK1 != sK1
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5199])).

cnf(c_6745,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(X0,sK1)
    | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8198,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_6745])).

cnf(c_8199,plain,
    ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(u1_pre_topc(sK0),sK1) = iProver_top
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8198])).

cnf(c_10928,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10111,c_27,c_28,c_24,c_1225,c_1228,c_1231,c_1368,c_1395,c_1397,c_1412,c_1414,c_1494,c_1555,c_1589,c_1717,c_1718,c_2474,c_2866,c_5200,c_5208,c_8055,c_8199])).

cnf(c_10933,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK0)
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10928,c_1013])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_77,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_81,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_20,plain,
    ( v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1253,plain,
    ( v2_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1257,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_448,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1506,plain,
    ( X0 != X1
    | u1_pre_topc(X2) != X1
    | u1_pre_topc(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_1853,plain,
    ( X0 != u1_pre_topc(X1)
    | u1_pre_topc(X2) = X0
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_3217,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(X0) = k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_3480,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
    | u1_pre_topc(sK1) = k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
    | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_1434,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != X0
    | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_3482,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
    | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
    | u1_pre_topc(sK1) != k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_458,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_3859,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_10941,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10933,c_26,c_25,c_28,c_23,c_22,c_77,c_81,c_1253,c_1257,c_3480,c_3482,c_3859,c_5508,c_7796])).

cnf(c_10946,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5688,c_10941])).

cnf(c_10947,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10946])).

cnf(c_6772,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(X0,sK1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8210,plain,
    ( v1_tops_2(u1_pre_topc(sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6772])).

cnf(c_6723,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8043,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_6723])).

cnf(c_5519,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5508])).

cnf(c_1532,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1490,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1221,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16877,c_16843,c_10947,c_8210,c_8043,c_5519,c_5207,c_5199,c_1718,c_1717,c_1588,c_1532,c_1490,c_1406,c_1407,c_1389,c_1390,c_1367,c_1230,c_1227,c_1221,c_24,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:00:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.84/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/0.98  
% 3.84/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.98  
% 3.84/0.98  ------  iProver source info
% 3.84/0.98  
% 3.84/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.98  git: non_committed_changes: false
% 3.84/0.98  git: last_make_outside_of_git: false
% 3.84/0.98  
% 3.84/0.98  ------ 
% 3.84/0.98  
% 3.84/0.98  ------ Input Options
% 3.84/0.98  
% 3.84/0.98  --out_options                           all
% 3.84/0.98  --tptp_safe_out                         true
% 3.84/0.98  --problem_path                          ""
% 3.84/0.98  --include_path                          ""
% 3.84/0.98  --clausifier                            res/vclausify_rel
% 3.84/0.98  --clausifier_options                    --mode clausify
% 3.84/0.98  --stdin                                 false
% 3.84/0.98  --stats_out                             sel
% 3.84/0.98  
% 3.84/0.98  ------ General Options
% 3.84/0.98  
% 3.84/0.98  --fof                                   false
% 3.84/0.98  --time_out_real                         604.99
% 3.84/0.98  --time_out_virtual                      -1.
% 3.84/0.98  --symbol_type_check                     false
% 3.84/0.98  --clausify_out                          false
% 3.84/0.98  --sig_cnt_out                           false
% 3.84/0.98  --trig_cnt_out                          false
% 3.84/0.98  --trig_cnt_out_tolerance                1.
% 3.84/0.98  --trig_cnt_out_sk_spl                   false
% 3.84/0.98  --abstr_cl_out                          false
% 3.84/0.98  
% 3.84/0.98  ------ Global Options
% 3.84/0.98  
% 3.84/0.98  --schedule                              none
% 3.84/0.98  --add_important_lit                     false
% 3.84/0.98  --prop_solver_per_cl                    1000
% 3.84/0.98  --min_unsat_core                        false
% 3.84/0.98  --soft_assumptions                      false
% 3.84/0.98  --soft_lemma_size                       3
% 3.84/0.98  --prop_impl_unit_size                   0
% 3.84/0.98  --prop_impl_unit                        []
% 3.84/0.98  --share_sel_clauses                     true
% 3.84/0.98  --reset_solvers                         false
% 3.84/0.98  --bc_imp_inh                            [conj_cone]
% 3.84/0.98  --conj_cone_tolerance                   3.
% 3.84/0.98  --extra_neg_conj                        none
% 3.84/0.98  --large_theory_mode                     true
% 3.84/0.98  --prolific_symb_bound                   200
% 3.84/0.98  --lt_threshold                          2000
% 3.84/0.98  --clause_weak_htbl                      true
% 3.84/0.98  --gc_record_bc_elim                     false
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing Options
% 3.84/0.98  
% 3.84/0.98  --preprocessing_flag                    true
% 3.84/0.98  --time_out_prep_mult                    0.1
% 3.84/0.98  --splitting_mode                        input
% 3.84/0.98  --splitting_grd                         true
% 3.84/0.98  --splitting_cvd                         false
% 3.84/0.98  --splitting_cvd_svl                     false
% 3.84/0.98  --splitting_nvd                         32
% 3.84/0.98  --sub_typing                            true
% 3.84/0.98  --prep_gs_sim                           false
% 3.84/0.98  --prep_unflatten                        true
% 3.84/0.98  --prep_res_sim                          true
% 3.84/0.98  --prep_upred                            true
% 3.84/0.98  --prep_sem_filter                       exhaustive
% 3.84/0.98  --prep_sem_filter_out                   false
% 3.84/0.98  --pred_elim                             false
% 3.84/0.98  --res_sim_input                         true
% 3.84/0.98  --eq_ax_congr_red                       true
% 3.84/0.98  --pure_diseq_elim                       true
% 3.84/0.98  --brand_transform                       false
% 3.84/0.98  --non_eq_to_eq                          false
% 3.84/0.98  --prep_def_merge                        true
% 3.84/0.98  --prep_def_merge_prop_impl              false
% 3.84/0.98  --prep_def_merge_mbd                    true
% 3.84/0.98  --prep_def_merge_tr_red                 false
% 3.84/0.98  --prep_def_merge_tr_cl                  false
% 3.84/0.98  --smt_preprocessing                     true
% 3.84/0.98  --smt_ac_axioms                         fast
% 3.84/0.98  --preprocessed_out                      false
% 3.84/0.98  --preprocessed_stats                    false
% 3.84/0.98  
% 3.84/0.98  ------ Abstraction refinement Options
% 3.84/0.98  
% 3.84/0.98  --abstr_ref                             []
% 3.84/0.98  --abstr_ref_prep                        false
% 3.84/0.98  --abstr_ref_until_sat                   false
% 3.84/0.98  --abstr_ref_sig_restrict                funpre
% 3.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.98  --abstr_ref_under                       []
% 3.84/0.98  
% 3.84/0.98  ------ SAT Options
% 3.84/0.98  
% 3.84/0.98  --sat_mode                              false
% 3.84/0.98  --sat_fm_restart_options                ""
% 3.84/0.98  --sat_gr_def                            false
% 3.84/0.98  --sat_epr_types                         true
% 3.84/0.98  --sat_non_cyclic_types                  false
% 3.84/0.98  --sat_finite_models                     false
% 3.84/0.98  --sat_fm_lemmas                         false
% 3.84/0.98  --sat_fm_prep                           false
% 3.84/0.98  --sat_fm_uc_incr                        true
% 3.84/0.98  --sat_out_model                         small
% 3.84/0.98  --sat_out_clauses                       false
% 3.84/0.98  
% 3.84/0.98  ------ QBF Options
% 3.84/0.98  
% 3.84/0.98  --qbf_mode                              false
% 3.84/0.98  --qbf_elim_univ                         false
% 3.84/0.98  --qbf_dom_inst                          none
% 3.84/0.98  --qbf_dom_pre_inst                      false
% 3.84/0.98  --qbf_sk_in                             false
% 3.84/0.98  --qbf_pred_elim                         true
% 3.84/0.98  --qbf_split                             512
% 3.84/0.98  
% 3.84/0.98  ------ BMC1 Options
% 3.84/0.98  
% 3.84/0.98  --bmc1_incremental                      false
% 3.84/0.98  --bmc1_axioms                           reachable_all
% 3.84/0.98  --bmc1_min_bound                        0
% 3.84/0.98  --bmc1_max_bound                        -1
% 3.84/0.98  --bmc1_max_bound_default                -1
% 3.84/0.98  --bmc1_symbol_reachability              true
% 3.84/0.98  --bmc1_property_lemmas                  false
% 3.84/0.98  --bmc1_k_induction                      false
% 3.84/0.98  --bmc1_non_equiv_states                 false
% 3.84/0.98  --bmc1_deadlock                         false
% 3.84/0.98  --bmc1_ucm                              false
% 3.84/0.98  --bmc1_add_unsat_core                   none
% 3.84/0.98  --bmc1_unsat_core_children              false
% 3.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.98  --bmc1_out_stat                         full
% 3.84/0.98  --bmc1_ground_init                      false
% 3.84/0.98  --bmc1_pre_inst_next_state              false
% 3.84/0.98  --bmc1_pre_inst_state                   false
% 3.84/0.98  --bmc1_pre_inst_reach_state             false
% 3.84/0.98  --bmc1_out_unsat_core                   false
% 3.84/0.98  --bmc1_aig_witness_out                  false
% 3.84/0.98  --bmc1_verbose                          false
% 3.84/0.98  --bmc1_dump_clauses_tptp                false
% 3.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.98  --bmc1_dump_file                        -
% 3.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.98  --bmc1_ucm_extend_mode                  1
% 3.84/0.98  --bmc1_ucm_init_mode                    2
% 3.84/0.98  --bmc1_ucm_cone_mode                    none
% 3.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.98  --bmc1_ucm_relax_model                  4
% 3.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.98  --bmc1_ucm_layered_model                none
% 3.84/0.98  --bmc1_ucm_max_lemma_size               10
% 3.84/0.98  
% 3.84/0.98  ------ AIG Options
% 3.84/0.98  
% 3.84/0.98  --aig_mode                              false
% 3.84/0.98  
% 3.84/0.98  ------ Instantiation Options
% 3.84/0.98  
% 3.84/0.98  --instantiation_flag                    true
% 3.84/0.98  --inst_sos_flag                         false
% 3.84/0.98  --inst_sos_phase                        true
% 3.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel_side                     num_symb
% 3.84/0.98  --inst_solver_per_active                1400
% 3.84/0.98  --inst_solver_calls_frac                1.
% 3.84/0.98  --inst_passive_queue_type               priority_queues
% 3.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.98  --inst_passive_queues_freq              [25;2]
% 3.84/0.98  --inst_dismatching                      true
% 3.84/0.98  --inst_eager_unprocessed_to_passive     true
% 3.84/0.98  --inst_prop_sim_given                   true
% 3.84/0.98  --inst_prop_sim_new                     false
% 3.84/0.98  --inst_subs_new                         false
% 3.84/0.98  --inst_eq_res_simp                      false
% 3.84/0.98  --inst_subs_given                       false
% 3.84/0.98  --inst_orphan_elimination               true
% 3.84/0.98  --inst_learning_loop_flag               true
% 3.84/0.98  --inst_learning_start                   3000
% 3.84/0.98  --inst_learning_factor                  2
% 3.84/0.98  --inst_start_prop_sim_after_learn       3
% 3.84/0.98  --inst_sel_renew                        solver
% 3.84/0.98  --inst_lit_activity_flag                true
% 3.84/0.98  --inst_restr_to_given                   false
% 3.84/0.98  --inst_activity_threshold               500
% 3.84/0.98  --inst_out_proof                        true
% 3.84/0.98  
% 3.84/0.98  ------ Resolution Options
% 3.84/0.98  
% 3.84/0.98  --resolution_flag                       true
% 3.84/0.98  --res_lit_sel                           adaptive
% 3.84/0.98  --res_lit_sel_side                      none
% 3.84/0.98  --res_ordering                          kbo
% 3.84/0.98  --res_to_prop_solver                    active
% 3.84/0.98  --res_prop_simpl_new                    false
% 3.84/0.98  --res_prop_simpl_given                  true
% 3.84/0.98  --res_passive_queue_type                priority_queues
% 3.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.98  --res_passive_queues_freq               [15;5]
% 3.84/0.98  --res_forward_subs                      full
% 3.84/0.98  --res_backward_subs                     full
% 3.84/0.98  --res_forward_subs_resolution           true
% 3.84/0.98  --res_backward_subs_resolution          true
% 3.84/0.98  --res_orphan_elimination                true
% 3.84/0.98  --res_time_limit                        2.
% 3.84/0.98  --res_out_proof                         true
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Options
% 3.84/0.98  
% 3.84/0.98  --superposition_flag                    true
% 3.84/0.98  --sup_passive_queue_type                priority_queues
% 3.84/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.98  --sup_passive_queues_freq               [1;4]
% 3.84/0.98  --demod_completeness_check              fast
% 3.84/0.98  --demod_use_ground                      true
% 3.84/0.98  --sup_to_prop_solver                    passive
% 3.84/0.98  --sup_prop_simpl_new                    true
% 3.84/0.98  --sup_prop_simpl_given                  true
% 3.84/0.98  --sup_fun_splitting                     false
% 3.84/0.98  --sup_smt_interval                      50000
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Simplification Setup
% 3.84/0.98  
% 3.84/0.98  --sup_indices_passive                   []
% 3.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.98  --sup_full_bw                           [BwDemod]
% 3.84/0.98  --sup_immed_triv                        [TrivRules]
% 3.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.98  --sup_immed_bw_main                     []
% 3.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.98  
% 3.84/0.98  ------ Combination Options
% 3.84/0.98  
% 3.84/0.98  --comb_res_mult                         3
% 3.84/0.98  --comb_sup_mult                         2
% 3.84/0.98  --comb_inst_mult                        10
% 3.84/0.98  
% 3.84/0.98  ------ Debug Options
% 3.84/0.98  
% 3.84/0.98  --dbg_backtrace                         false
% 3.84/0.98  --dbg_dump_prop_clauses                 false
% 3.84/0.98  --dbg_dump_prop_clauses_file            -
% 3.84/0.98  --dbg_out_stat                          false
% 3.84/0.98  ------ Parsing...
% 3.84/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/0.98  ------ Proving...
% 3.84/0.98  ------ Problem Properties 
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  clauses                                 25
% 3.84/0.98  conjectures                             5
% 3.84/0.98  EPR                                     9
% 3.84/0.98  Horn                                    25
% 3.84/0.98  unary                                   6
% 3.84/0.98  binary                                  4
% 3.84/0.98  lits                                    71
% 3.84/0.98  lits eq                                 4
% 3.84/0.98  fd_pure                                 0
% 3.84/0.98  fd_pseudo                               0
% 3.84/0.98  fd_cond                                 0
% 3.84/0.98  fd_pseudo_cond                          1
% 3.84/0.98  AC symbols                              0
% 3.84/0.98  
% 3.84/0.98  ------ Input Options Time Limit: Unbounded
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  ------ 
% 3.84/0.98  Current options:
% 3.84/0.98  ------ 
% 3.84/0.98  
% 3.84/0.98  ------ Input Options
% 3.84/0.98  
% 3.84/0.98  --out_options                           all
% 3.84/0.98  --tptp_safe_out                         true
% 3.84/0.98  --problem_path                          ""
% 3.84/0.98  --include_path                          ""
% 3.84/0.98  --clausifier                            res/vclausify_rel
% 3.84/0.98  --clausifier_options                    --mode clausify
% 3.84/0.98  --stdin                                 false
% 3.84/0.98  --stats_out                             sel
% 3.84/0.98  
% 3.84/0.98  ------ General Options
% 3.84/0.98  
% 3.84/0.98  --fof                                   false
% 3.84/0.98  --time_out_real                         604.99
% 3.84/0.98  --time_out_virtual                      -1.
% 3.84/0.98  --symbol_type_check                     false
% 3.84/0.98  --clausify_out                          false
% 3.84/0.98  --sig_cnt_out                           false
% 3.84/0.98  --trig_cnt_out                          false
% 3.84/0.98  --trig_cnt_out_tolerance                1.
% 3.84/0.98  --trig_cnt_out_sk_spl                   false
% 3.84/0.98  --abstr_cl_out                          false
% 3.84/0.98  
% 3.84/0.98  ------ Global Options
% 3.84/0.98  
% 3.84/0.98  --schedule                              none
% 3.84/0.98  --add_important_lit                     false
% 3.84/0.98  --prop_solver_per_cl                    1000
% 3.84/0.98  --min_unsat_core                        false
% 3.84/0.98  --soft_assumptions                      false
% 3.84/0.98  --soft_lemma_size                       3
% 3.84/0.98  --prop_impl_unit_size                   0
% 3.84/0.98  --prop_impl_unit                        []
% 3.84/0.98  --share_sel_clauses                     true
% 3.84/0.98  --reset_solvers                         false
% 3.84/0.98  --bc_imp_inh                            [conj_cone]
% 3.84/0.98  --conj_cone_tolerance                   3.
% 3.84/0.98  --extra_neg_conj                        none
% 3.84/0.98  --large_theory_mode                     true
% 3.84/0.98  --prolific_symb_bound                   200
% 3.84/0.98  --lt_threshold                          2000
% 3.84/0.98  --clause_weak_htbl                      true
% 3.84/0.98  --gc_record_bc_elim                     false
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing Options
% 3.84/0.98  
% 3.84/0.98  --preprocessing_flag                    true
% 3.84/0.98  --time_out_prep_mult                    0.1
% 3.84/0.98  --splitting_mode                        input
% 3.84/0.98  --splitting_grd                         true
% 3.84/0.98  --splitting_cvd                         false
% 3.84/0.98  --splitting_cvd_svl                     false
% 3.84/0.98  --splitting_nvd                         32
% 3.84/0.98  --sub_typing                            true
% 3.84/0.98  --prep_gs_sim                           false
% 3.84/0.98  --prep_unflatten                        true
% 3.84/0.98  --prep_res_sim                          true
% 3.84/0.98  --prep_upred                            true
% 3.84/0.98  --prep_sem_filter                       exhaustive
% 3.84/0.98  --prep_sem_filter_out                   false
% 3.84/0.98  --pred_elim                             false
% 3.84/0.98  --res_sim_input                         true
% 3.84/0.98  --eq_ax_congr_red                       true
% 3.84/0.98  --pure_diseq_elim                       true
% 3.84/0.98  --brand_transform                       false
% 3.84/0.98  --non_eq_to_eq                          false
% 3.84/0.98  --prep_def_merge                        true
% 3.84/0.98  --prep_def_merge_prop_impl              false
% 3.84/0.98  --prep_def_merge_mbd                    true
% 3.84/0.98  --prep_def_merge_tr_red                 false
% 3.84/0.98  --prep_def_merge_tr_cl                  false
% 3.84/0.98  --smt_preprocessing                     true
% 3.84/0.98  --smt_ac_axioms                         fast
% 3.84/0.98  --preprocessed_out                      false
% 3.84/0.98  --preprocessed_stats                    false
% 3.84/0.98  
% 3.84/0.98  ------ Abstraction refinement Options
% 3.84/0.98  
% 3.84/0.98  --abstr_ref                             []
% 3.84/0.98  --abstr_ref_prep                        false
% 3.84/0.98  --abstr_ref_until_sat                   false
% 3.84/0.98  --abstr_ref_sig_restrict                funpre
% 3.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.98  --abstr_ref_under                       []
% 3.84/0.98  
% 3.84/0.98  ------ SAT Options
% 3.84/0.98  
% 3.84/0.98  --sat_mode                              false
% 3.84/0.98  --sat_fm_restart_options                ""
% 3.84/0.98  --sat_gr_def                            false
% 3.84/0.98  --sat_epr_types                         true
% 3.84/0.98  --sat_non_cyclic_types                  false
% 3.84/0.98  --sat_finite_models                     false
% 3.84/0.98  --sat_fm_lemmas                         false
% 3.84/0.98  --sat_fm_prep                           false
% 3.84/0.98  --sat_fm_uc_incr                        true
% 3.84/0.98  --sat_out_model                         small
% 3.84/0.98  --sat_out_clauses                       false
% 3.84/0.98  
% 3.84/0.98  ------ QBF Options
% 3.84/0.98  
% 3.84/0.98  --qbf_mode                              false
% 3.84/0.98  --qbf_elim_univ                         false
% 3.84/0.98  --qbf_dom_inst                          none
% 3.84/0.98  --qbf_dom_pre_inst                      false
% 3.84/0.98  --qbf_sk_in                             false
% 3.84/0.98  --qbf_pred_elim                         true
% 3.84/0.98  --qbf_split                             512
% 3.84/0.98  
% 3.84/0.98  ------ BMC1 Options
% 3.84/0.98  
% 3.84/0.98  --bmc1_incremental                      false
% 3.84/0.98  --bmc1_axioms                           reachable_all
% 3.84/0.98  --bmc1_min_bound                        0
% 3.84/0.98  --bmc1_max_bound                        -1
% 3.84/0.98  --bmc1_max_bound_default                -1
% 3.84/0.98  --bmc1_symbol_reachability              true
% 3.84/0.98  --bmc1_property_lemmas                  false
% 3.84/0.98  --bmc1_k_induction                      false
% 3.84/0.98  --bmc1_non_equiv_states                 false
% 3.84/0.98  --bmc1_deadlock                         false
% 3.84/0.98  --bmc1_ucm                              false
% 3.84/0.98  --bmc1_add_unsat_core                   none
% 3.84/0.98  --bmc1_unsat_core_children              false
% 3.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.98  --bmc1_out_stat                         full
% 3.84/0.98  --bmc1_ground_init                      false
% 3.84/0.98  --bmc1_pre_inst_next_state              false
% 3.84/0.98  --bmc1_pre_inst_state                   false
% 3.84/0.98  --bmc1_pre_inst_reach_state             false
% 3.84/0.98  --bmc1_out_unsat_core                   false
% 3.84/0.98  --bmc1_aig_witness_out                  false
% 3.84/0.98  --bmc1_verbose                          false
% 3.84/0.98  --bmc1_dump_clauses_tptp                false
% 3.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.98  --bmc1_dump_file                        -
% 3.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.98  --bmc1_ucm_extend_mode                  1
% 3.84/0.98  --bmc1_ucm_init_mode                    2
% 3.84/0.98  --bmc1_ucm_cone_mode                    none
% 3.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.98  --bmc1_ucm_relax_model                  4
% 3.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.98  --bmc1_ucm_layered_model                none
% 3.84/0.98  --bmc1_ucm_max_lemma_size               10
% 3.84/0.98  
% 3.84/0.98  ------ AIG Options
% 3.84/0.98  
% 3.84/0.98  --aig_mode                              false
% 3.84/0.98  
% 3.84/0.98  ------ Instantiation Options
% 3.84/0.98  
% 3.84/0.98  --instantiation_flag                    true
% 3.84/0.98  --inst_sos_flag                         false
% 3.84/0.98  --inst_sos_phase                        true
% 3.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel_side                     num_symb
% 3.84/0.98  --inst_solver_per_active                1400
% 3.84/0.98  --inst_solver_calls_frac                1.
% 3.84/0.98  --inst_passive_queue_type               priority_queues
% 3.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.98  --inst_passive_queues_freq              [25;2]
% 3.84/0.98  --inst_dismatching                      true
% 3.84/0.98  --inst_eager_unprocessed_to_passive     true
% 3.84/0.98  --inst_prop_sim_given                   true
% 3.84/0.98  --inst_prop_sim_new                     false
% 3.84/0.98  --inst_subs_new                         false
% 3.84/0.98  --inst_eq_res_simp                      false
% 3.84/0.98  --inst_subs_given                       false
% 3.84/0.98  --inst_orphan_elimination               true
% 3.84/0.98  --inst_learning_loop_flag               true
% 3.84/0.98  --inst_learning_start                   3000
% 3.84/0.98  --inst_learning_factor                  2
% 3.84/0.98  --inst_start_prop_sim_after_learn       3
% 3.84/0.98  --inst_sel_renew                        solver
% 3.84/0.98  --inst_lit_activity_flag                true
% 3.84/0.98  --inst_restr_to_given                   false
% 3.84/0.98  --inst_activity_threshold               500
% 3.84/0.98  --inst_out_proof                        true
% 3.84/0.98  
% 3.84/0.98  ------ Resolution Options
% 3.84/0.98  
% 3.84/0.98  --resolution_flag                       true
% 3.84/0.98  --res_lit_sel                           adaptive
% 3.84/0.98  --res_lit_sel_side                      none
% 3.84/0.98  --res_ordering                          kbo
% 3.84/0.98  --res_to_prop_solver                    active
% 3.84/0.98  --res_prop_simpl_new                    false
% 3.84/0.98  --res_prop_simpl_given                  true
% 3.84/0.98  --res_passive_queue_type                priority_queues
% 3.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.98  --res_passive_queues_freq               [15;5]
% 3.84/0.98  --res_forward_subs                      full
% 3.84/0.98  --res_backward_subs                     full
% 3.84/0.98  --res_forward_subs_resolution           true
% 3.84/0.98  --res_backward_subs_resolution          true
% 3.84/0.98  --res_orphan_elimination                true
% 3.84/0.98  --res_time_limit                        2.
% 3.84/0.98  --res_out_proof                         true
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Options
% 3.84/0.98  
% 3.84/0.98  --superposition_flag                    true
% 3.84/0.98  --sup_passive_queue_type                priority_queues
% 3.84/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.98  --sup_passive_queues_freq               [1;4]
% 3.84/0.98  --demod_completeness_check              fast
% 3.84/0.98  --demod_use_ground                      true
% 3.84/0.98  --sup_to_prop_solver                    passive
% 3.84/0.98  --sup_prop_simpl_new                    true
% 3.84/0.98  --sup_prop_simpl_given                  true
% 3.84/0.98  --sup_fun_splitting                     false
% 3.84/0.98  --sup_smt_interval                      50000
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Simplification Setup
% 3.84/0.98  
% 3.84/0.98  --sup_indices_passive                   []
% 3.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.98  --sup_full_bw                           [BwDemod]
% 3.84/0.98  --sup_immed_triv                        [TrivRules]
% 3.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.98  --sup_immed_bw_main                     []
% 3.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.98  
% 3.84/0.98  ------ Combination Options
% 3.84/0.98  
% 3.84/0.98  --comb_res_mult                         3
% 3.84/0.98  --comb_sup_mult                         2
% 3.84/0.98  --comb_inst_mult                        10
% 3.84/0.98  
% 3.84/0.98  ------ Debug Options
% 3.84/0.98  
% 3.84/0.98  --dbg_backtrace                         false
% 3.84/0.98  --dbg_dump_prop_clauses                 false
% 3.84/0.98  --dbg_dump_prop_clauses_file            -
% 3.84/0.98  --dbg_out_stat                          false
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  ------ Proving...
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  % SZS status Theorem for theBenchmark.p
% 3.84/0.98  
% 3.84/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.98  
% 3.84/0.98  fof(f9,axiom,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f25,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f9])).
% 3.84/0.98  
% 3.84/0.98  fof(f26,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(flattening,[],[f25])).
% 3.84/0.98  
% 3.84/0.98  fof(f60,plain,(
% 3.84/0.98    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f26])).
% 3.84/0.98  
% 3.84/0.98  fof(f80,plain,(
% 3.84/0.98    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(equality_resolution,[],[f60])).
% 3.84/0.98  
% 3.84/0.98  fof(f8,axiom,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f24,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f8])).
% 3.84/0.98  
% 3.84/0.98  fof(f59,plain,(
% 3.84/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f24])).
% 3.84/0.98  
% 3.84/0.98  fof(f5,axiom,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f21,plain,(
% 3.84/0.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f5])).
% 3.84/0.98  
% 3.84/0.98  fof(f55,plain,(
% 3.84/0.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f21])).
% 3.84/0.98  
% 3.84/0.98  fof(f4,axiom,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f20,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f4])).
% 3.84/0.98  
% 3.84/0.98  fof(f54,plain,(
% 3.84/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f20])).
% 3.84/0.98  
% 3.84/0.98  fof(f10,axiom,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f27,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f10])).
% 3.84/0.98  
% 3.84/0.98  fof(f42,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(nnf_transformation,[],[f27])).
% 3.84/0.98  
% 3.84/0.98  fof(f61,plain,(
% 3.84/0.98    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f42])).
% 3.84/0.98  
% 3.84/0.98  fof(f12,axiom,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f29,plain,(
% 3.84/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f12])).
% 3.84/0.98  
% 3.84/0.98  fof(f64,plain,(
% 3.84/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f29])).
% 3.84/0.98  
% 3.84/0.98  fof(f7,axiom,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f23,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f7])).
% 3.84/0.98  
% 3.84/0.98  fof(f41,plain,(
% 3.84/0.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.84/0.98    inference(nnf_transformation,[],[f23])).
% 3.84/0.98  
% 3.84/0.98  fof(f57,plain,(
% 3.84/0.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f41])).
% 3.84/0.98  
% 3.84/0.98  fof(f17,conjecture,(
% 3.84/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 3.84/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f18,negated_conjecture,(
% 3.84/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 3.84/0.98    inference(negated_conjecture,[],[f17])).
% 3.84/0.98  
% 3.84/0.98  fof(f36,plain,(
% 3.84/0.98    ? [X0] : (? [X1] : ((~v2_tdlat_3(X1) & (v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.84/0.98    inference(ennf_transformation,[],[f18])).
% 3.84/0.99  
% 3.84/0.99  fof(f37,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f36])).
% 3.84/0.99  
% 3.84/0.99  fof(f46,plain,(
% 3.84/0.99    ( ! [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v2_tdlat_3(sK1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK1))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f45,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f47,plain,(
% 3.84/0.99    (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f46,f45])).
% 3.84/0.99  
% 3.84/0.99  fof(f73,plain,(
% 3.84/0.99    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 3.84/0.99    inference(cnf_transformation,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f6,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f22,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f6])).
% 3.84/0.99  
% 3.84/0.99  fof(f56,plain,(
% 3.84/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f22])).
% 3.84/0.99  
% 3.84/0.99  fof(f71,plain,(
% 3.84/0.99    l1_pre_topc(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f72,plain,(
% 3.84/0.99    l1_pre_topc(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f14,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f31,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f32,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f31])).
% 3.84/0.99  
% 3.84/0.99  fof(f43,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f32])).
% 3.84/0.99  
% 3.84/0.99  fof(f67,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f43])).
% 3.84/0.99  
% 3.84/0.99  fof(f74,plain,(
% 3.84/0.99    v2_tdlat_3(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f15,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f33,plain,(
% 3.84/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f15])).
% 3.84/0.99  
% 3.84/0.99  fof(f34,plain,(
% 3.84/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f68,plain,(
% 3.84/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f1,axiom,(
% 3.84/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f38,plain,(
% 3.84/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.99    inference(nnf_transformation,[],[f1])).
% 3.84/0.99  
% 3.84/0.99  fof(f39,plain,(
% 3.84/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.99    inference(flattening,[],[f38])).
% 3.84/0.99  
% 3.84/0.99  fof(f50,plain,(
% 3.84/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f39])).
% 3.84/0.99  
% 3.84/0.99  fof(f13,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f30,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f13])).
% 3.84/0.99  
% 3.84/0.99  fof(f65,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f30])).
% 3.84/0.99  
% 3.84/0.99  fof(f11,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f19,plain,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 3.84/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.84/0.99  
% 3.84/0.99  fof(f28,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f19])).
% 3.84/0.99  
% 3.84/0.99  fof(f63,plain,(
% 3.84/0.99    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f28])).
% 3.84/0.99  
% 3.84/0.99  fof(f48,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.84/0.99    inference(cnf_transformation,[],[f39])).
% 3.84/0.99  
% 3.84/0.99  fof(f79,plain,(
% 3.84/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/0.99    inference(equality_resolution,[],[f48])).
% 3.84/0.99  
% 3.84/0.99  fof(f62,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f42])).
% 3.84/0.99  
% 3.84/0.99  fof(f75,plain,(
% 3.84/0.99    ~v2_tdlat_3(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f16,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) <=> k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f35,plain,(
% 3.84/0.99    ! [X0] : ((v2_tdlat_3(X0) <=> k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f16])).
% 3.84/0.99  
% 3.84/0.99  fof(f44,plain,(
% 3.84/0.99    ! [X0] : (((v2_tdlat_3(X0) | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0)) & (k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f35])).
% 3.84/0.99  
% 3.84/0.99  fof(f70,plain,(
% 3.84/0.99    ( ! [X0] : (v2_tdlat_3(X0) | k2_tarski(k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f44])).
% 3.84/0.99  
% 3.84/0.99  fof(f2,axiom,(
% 3.84/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f51,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f2])).
% 3.84/0.99  
% 3.84/0.99  fof(f76,plain,(
% 3.84/0.99    ( ! [X0] : (v2_tdlat_3(X0) | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(definition_unfolding,[],[f70,f51])).
% 3.84/0.99  
% 3.84/0.99  fof(f69,plain,(
% 3.84/0.99    ( ! [X0] : (k2_tarski(k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f44])).
% 3.84/0.99  
% 3.84/0.99  fof(f77,plain,(
% 3.84/0.99    ( ! [X0] : (k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(definition_unfolding,[],[f69,f51])).
% 3.84/0.99  
% 3.84/0.99  cnf(c_11,plain,
% 3.84/0.99      ( ~ v1_tops_2(X0,X1)
% 3.84/0.99      | v1_tops_2(X0,X2)
% 3.84/0.99      | ~ m1_pre_topc(X2,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1631,plain,
% 3.84/0.99      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | v1_tops_2(X0,sK0)
% 3.84/0.99      | ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_16877,plain,
% 3.84/0.99      ( ~ v1_tops_2(u1_pre_topc(sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | v1_tops_2(u1_pre_topc(sK1),sK0)
% 3.84/0.99      | ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1631]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1670,plain,
% 3.84/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_16843,plain,
% 3.84/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1670]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.84/0.99      | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1008,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.84/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1006,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2968,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 3.84/0.99      | l1_pre_topc(X0) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1008,c_1006]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_69,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5677,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2968,c_69]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5678,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_5677]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_13,plain,
% 3.84/0.99      ( ~ v1_tops_2(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.84/0.99      | r1_tarski(X0,u1_pre_topc(X1))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1003,plain,
% 3.84/0.99      ( v1_tops_2(X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5688,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(X0),X1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | r1_tarski(u1_pre_topc(X0),u1_pre_topc(X1)) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5678,c_1003]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_15,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1001,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.84/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X0)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_248,plain,
% 3.84/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.84/0.99      | ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_249,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_248]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_990,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_24,negated_conjecture,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1007,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2228,plain,
% 3.84/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK0) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_24,c_1007]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_26,negated_conjecture,
% 3.84/0.99      ( l1_pre_topc(sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_27,plain,
% 3.84/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2528,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2228,c_27]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2529,plain,
% 3.84/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK0) = iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_2528]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2536,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_990,c_2529]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_25,negated_conjecture,
% 3.84/0.99      ( l1_pre_topc(sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_28,plain,
% 3.84/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5499,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK0) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2536,c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5500,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_5499]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5508,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1001,c_5500]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5522,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5508,c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_17,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_pre_topc(X2,X1)
% 3.84/0.99      | ~ m1_pre_topc(X0,X2)
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.84/0.99      | ~ v2_pre_topc(X1)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_999,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.84/0.99      | v2_pre_topc(X1) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5530,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 3.84/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5522,c_999]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_23,negated_conjecture,
% 3.84/0.99      ( v2_tdlat_3(sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_29,plain,
% 3.84/0.99      ( v2_tdlat_3(sK0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_19,plain,
% 3.84/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1233,plain,
% 3.84/0.99      ( ~ v2_tdlat_3(sK0) | v2_pre_topc(sK0) | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1234,plain,
% 3.84/0.99      ( v2_tdlat_3(sK0) != iProver_top
% 3.84/0.99      | v2_pre_topc(sK0) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8576,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5530,c_27,c_29,c_1234]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_0,plain,
% 3.84/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.84/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1013,plain,
% 3.84/0.99      ( X0 = X1
% 3.84/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.84/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8585,plain,
% 3.84/0.99      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 3.84/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_8576,c_1013]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1241,plain,
% 3.84/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_24,c_990]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2259,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_1241,c_27]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2260,plain,
% 3.84/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK0) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_2259]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2268,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK1) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2260,c_1007]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1422,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.84/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.84/0.99      | ~ v2_pre_topc(sK0)
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7713,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.84/0.99      | ~ m1_pre_topc(X0,sK1)
% 3.84/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))
% 3.84/0.99      | ~ v2_pre_topc(sK0)
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1422]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7717,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
% 3.84/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_7713]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8605,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,X0) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | u1_struct_0(X0) = u1_struct_0(sK1) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_8585,c_27,c_28,c_29,c_1234,c_2268,c_5508,c_7717]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8606,plain,
% 3.84/0.99      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 3.84/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,X0) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_8605]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8615,plain,
% 3.84/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK0)
% 3.84/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1001,c_8606]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3289,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK0) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2268,c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3290,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,sK1) = iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_3289]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3298,plain,
% 3.84/0.99      ( m1_pre_topc(sK0,sK1) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1001,c_3290]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3392,plain,
% 3.84/0.99      ( m1_pre_topc(sK0,sK1) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3298,c_27]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_16,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1000,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2012,plain,
% 3.84/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.84/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1000,c_1013]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3418,plain,
% 3.84/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.84/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1000,c_2012]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_44,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7779,plain,
% 3.84/0.99      ( l1_pre_topc(X1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.84/0.99      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3418,c_44,c_69,c_2012]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7780,plain,
% 3.84/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.84/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.84/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_7779]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7796,plain,
% 3.84/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK0)
% 3.84/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3392,c_7780]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9518,plain,
% 3.84/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_8615,c_28,c_5508,c_7796]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9566,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_9518,c_1008]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1224,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1225,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1224]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1227,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1228,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1230,plain,
% 3.84/0.99      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1231,plain,
% 3.84/0.99      ( m1_pre_topc(sK0,sK0) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_452,plain,
% 3.84/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 3.84/0.99      theory(equality) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1367,plain,
% 3.84/0.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.84/0.99      inference(resolution,[status(thm)],[c_452,c_24]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1368,plain,
% 3.84/0.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.84/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1367]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_14,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1390,plain,
% 3.84/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 3.84/0.99      | ~ m1_pre_topc(sK1,sK1)
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1395,plain,
% 3.84/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1390]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1406,plain,
% 3.84/0.99      ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ m1_pre_topc(sK0,sK0)
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_249]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1414,plain,
% 3.84/0.99      ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1588,plain,
% 3.84/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 3.84/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1589,plain,
% 3.84/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 3.84/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1436,plain,
% 3.84/0.99      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | X0 = sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1717,plain,
% 3.84/0.99      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2,plain,
% 3.84/0.99      ( r1_tarski(X0,X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1718,plain,
% 3.84/0.99      ( r1_tarski(sK1,sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1611,plain,
% 3.84/0.99      ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2473,plain,
% 3.84/0.99      ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1611]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2474,plain,
% 3.84/0.99      ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.84/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2473]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_453,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.84/0.99      theory(equality) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1583,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 3.84/0.99      | X0 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | X1 != sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2691,plain,
% 3.84/0.99      ( m1_pre_topc(X0,sK1)
% 3.84/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 3.84/0.99      | X0 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | sK1 != sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1583]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5207,plain,
% 3.84/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.84/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
% 3.84/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | sK1 != sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2691]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5208,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | sK1 != sK1
% 3.84/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.84/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_5207]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6751,plain,
% 3.84/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8054,plain,
% 3.84/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6751]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8055,plain,
% 3.84/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_8054]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10102,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_9566,c_27,c_28,c_24,c_1225,c_1228,c_1231,c_1368,
% 3.84/0.99                 c_1395,c_1414,c_1589,c_1717,c_1718,c_2474,c_5208,c_8055]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10111,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK0),sK1) != iProver_top
% 3.84/0.99      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_10102,c_1003]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1389,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.84/0.99      | ~ m1_pre_topc(sK1,sK1)
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_249]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1397,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1389]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1407,plain,
% 3.84/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
% 3.84/0.99      | ~ m1_pre_topc(sK0,sK0)
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1412,plain,
% 3.84/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1407]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12,plain,
% 3.84/0.99      ( v1_tops_2(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.84/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1305,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(X0),X0)
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.84/0.99      | ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
% 3.84/0.99      | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1493,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK0),sK0)
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1494,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK0),sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.84/0.99      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1493]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1304,plain,
% 3.84/0.99      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1554,plain,
% 3.84/0.99      ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1555,plain,
% 3.84/0.99      ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1554]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1691,plain,
% 3.84/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ v1_tops_2(X0,sK0)
% 3.84/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2865,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
% 3.84/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1691]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2866,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.84/0.99      | v1_tops_2(u1_pre_topc(sK0),sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2865]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1557,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.84/0.99      | X1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | X0 != sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2682,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,X0)
% 3.84/0.99      | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.84/0.99      | X0 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | sK1 != sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1557]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5199,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | sK1 != sK1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2682]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5200,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | sK1 != sK1
% 3.84/0.99      | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_5199]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6745,plain,
% 3.84/0.99      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | v1_tops_2(X0,sK1)
% 3.84/0.99      | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8198,plain,
% 3.84/0.99      ( ~ v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | v1_tops_2(u1_pre_topc(sK0),sK1)
% 3.84/0.99      | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6745]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8199,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.84/0.99      | v1_tops_2(u1_pre_topc(sK0),sK1) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_8198]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10928,plain,
% 3.84/0.99      ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_10111,c_27,c_28,c_24,c_1225,c_1228,c_1231,c_1368,
% 3.84/0.99                 c_1395,c_1397,c_1412,c_1414,c_1494,c_1555,c_1589,c_1717,
% 3.84/0.99                 c_1718,c_2474,c_2866,c_5200,c_5208,c_8055,c_8199]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10933,plain,
% 3.84/0.99      ( u1_pre_topc(sK1) = u1_pre_topc(sK0)
% 3.84/0.99      | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_10928,c_1013]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_22,negated_conjecture,
% 3.84/0.99      ( ~ v2_tdlat_3(sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_77,plain,
% 3.84/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_81,plain,
% 3.84/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.84/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_20,plain,
% 3.84/0.99      ( v2_tdlat_3(X0)
% 3.84/0.99      | ~ l1_pre_topc(X0)
% 3.84/0.99      | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) != u1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1253,plain,
% 3.84/0.99      ( v2_tdlat_3(sK1)
% 3.84/0.99      | ~ l1_pre_topc(sK1)
% 3.84/0.99      | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != u1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_21,plain,
% 3.84/0.99      ( ~ v2_tdlat_3(X0)
% 3.84/0.99      | ~ l1_pre_topc(X0)
% 3.84/0.99      | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) = u1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1257,plain,
% 3.84/0.99      ( ~ v2_tdlat_3(sK0)
% 3.84/0.99      | ~ l1_pre_topc(sK0)
% 3.84/0.99      | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_448,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1506,plain,
% 3.84/0.99      ( X0 != X1 | u1_pre_topc(X2) != X1 | u1_pre_topc(X2) = X0 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_448]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1853,plain,
% 3.84/0.99      ( X0 != u1_pre_topc(X1)
% 3.84/0.99      | u1_pre_topc(X2) = X0
% 3.84/0.99      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3217,plain,
% 3.84/0.99      ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 3.84/0.99      | u1_pre_topc(X0) = k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
% 3.84/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1853]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3480,plain,
% 3.84/0.99      ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) != u1_pre_topc(sK0)
% 3.84/0.99      | u1_pre_topc(sK1) = k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
% 3.84/0.99      | u1_pre_topc(sK1) != u1_pre_topc(sK0) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_3217]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1434,plain,
% 3.84/0.99      ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != X0
% 3.84/0.99      | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 3.84/0.99      | u1_pre_topc(sK1) != X0 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_448]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3482,plain,
% 3.84/0.99      ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) != k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
% 3.84/0.99      | k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = u1_pre_topc(sK1)
% 3.84/0.99      | u1_pre_topc(sK1) != k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1434]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_458,plain,
% 3.84/0.99      ( X0 != X1
% 3.84/0.99      | X2 != X3
% 3.84/0.99      | X4 != X5
% 3.84/0.99      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 3.84/0.99      theory(equality) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3859,plain,
% 3.84/0.99      ( k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) = k1_enumset1(k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
% 3.84/0.99      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 3.84/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_458]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10941,plain,
% 3.84/0.99      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_10933,c_26,c_25,c_28,c_23,c_22,c_77,c_81,c_1253,
% 3.84/0.99                 c_1257,c_3480,c_3482,c_3859,c_5508,c_7796]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10946,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK1),sK0) != iProver_top
% 3.84/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5688,c_10941]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10947,plain,
% 3.84/0.99      ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
% 3.84/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_10946]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6772,plain,
% 3.84/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ v1_tops_2(X0,sK1)
% 3.84/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8210,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
% 3.84/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6772]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6723,plain,
% 3.84/0.99      ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8043,plain,
% 3.84/0.99      ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.84/0.99      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6723]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5519,plain,
% 3.84/0.99      ( m1_pre_topc(sK1,sK0) | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5508]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1532,plain,
% 3.84/0.99      ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1490,plain,
% 3.84/0.99      ( v1_tops_2(u1_pre_topc(sK1),sK1)
% 3.84/0.99      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1221,plain,
% 3.84/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.84/0.99      | ~ l1_pre_topc(sK1) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(contradiction,plain,
% 3.84/0.99      ( $false ),
% 3.84/0.99      inference(minisat,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_16877,c_16843,c_10947,c_8210,c_8043,c_5519,c_5207,
% 3.84/0.99                 c_5199,c_1718,c_1717,c_1588,c_1532,c_1490,c_1406,c_1407,
% 3.84/0.99                 c_1389,c_1390,c_1367,c_1230,c_1227,c_1221,c_24,c_25,
% 3.84/0.99                 c_26]) ).
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  ------                               Statistics
% 3.84/0.99  
% 3.84/0.99  ------ Selected
% 3.84/0.99  
% 3.84/0.99  total_time:                             0.471
% 3.84/0.99  
%------------------------------------------------------------------------------
