%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:09 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  191 (4028 expanded)
%              Number of clauses        :  137 (1558 expanded)
%              Number of leaves         :   17 ( 755 expanded)
%              Depth                    :   30
%              Number of atoms          :  640 (18320 expanded)
%              Number of equality atoms :  258 (2494 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_compts_1(X2,X0)
                      | ~ v2_compts_1(X3,X1) )
                    & ( v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f33,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f35,plain,(
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
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v2_compts_1(sK1,X0) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(sK1,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f51,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_895,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12103,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_12675,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_12103])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_642,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_653,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1146,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_656])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_657,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_657,c_0])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_652,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1350,plain,
    ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_652])).

cnf(c_1772,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) = u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1350])).

cnf(c_10212,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(superposition,[status(thm)],[c_642,c_1772])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_646,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_655,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1562,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_655])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_38,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_40,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_809,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_810,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_812,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_2082,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1562,c_19,c_40,c_812])).

cnf(c_2083,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2082])).

cnf(c_8,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_650,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2089,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2083,c_650])).

cnf(c_4293,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2089,c_19])).

cnf(c_4294,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4293])).

cnf(c_1348,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_652])).

cnf(c_1409,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_19,c_40,c_812])).

cnf(c_1410,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_1409])).

cnf(c_1771,plain,
    ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_642,c_1350])).

cnf(c_1796,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0),k1_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_655])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_651,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1614,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_651])).

cnf(c_2692,plain,
    ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_652])).

cnf(c_3582,plain,
    ( u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_2692])).

cnf(c_1565,plain,
    ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_655])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_654,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2441,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_654])).

cnf(c_2466,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_8478,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3582,c_19,c_2466])).

cnf(c_8479,plain,
    ( u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8478])).

cnf(c_8487,plain,
    ( u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK1)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK1))
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1410,c_8479])).

cnf(c_39,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_811,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_97,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_4])).

cnf(c_98,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_97])).

cnf(c_873,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_319,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_913,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_822,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1052,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_320,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1136,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_1871,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_2284,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1
    | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2320,plain,
    ( k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1564,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_655])).

cnf(c_4178,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1564,c_19])).

cnf(c_4179,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4178])).

cnf(c_4180,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4179])).

cnf(c_1415,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_652])).

cnf(c_1418,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1415,c_19])).

cnf(c_1419,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(renaming,[status(thm)],[c_1418])).

cnf(c_1422,plain,
    ( u1_struct_0(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)) = X0
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_652])).

cnf(c_836,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2103,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2089])).

cnf(c_2685,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_1614])).

cnf(c_2778,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2685])).

cnf(c_2780,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_2778])).

cnf(c_4476,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_18,c_836,c_2103,c_2780])).

cnf(c_2825,plain,
    ( X0 != u1_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 = X0
    | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_5373,plain,
    ( k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != u1_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 = k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_1019,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5499,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_839,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_1087,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
    | X0 != k2_subset_1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1948,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | X0 != k2_subset_1(u1_struct_0(X1))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_6689,plain,
    ( ~ m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | sK1 != k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_1088,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_8387,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_8587,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8487,c_18,c_39,c_811,c_836,c_873,c_913,c_1004,c_1052,c_2103,c_2284,c_2320,c_2780,c_4180,c_5373,c_5499,c_6689,c_8387])).

cnf(c_8603,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8587,c_1614])).

cnf(c_9413,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4294,c_8603])).

cnf(c_9446,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9413,c_19])).

cnf(c_9454,plain,
    ( m1_pre_topc(sK0,X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9446,c_651])).

cnf(c_10780,plain,
    ( m1_pre_topc(sK0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10212,c_9454])).

cnf(c_831,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_832,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_874,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_1055,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_5505,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5499])).

cnf(c_6690,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | sK1 != k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6689])).

cnf(c_12463,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10780,c_18,c_19,c_40,c_812,c_832,c_836,c_874,c_913,c_1055,c_2103,c_2284,c_2320,c_2780,c_5373,c_5505,c_6690,c_8387,c_9413])).

cnf(c_13,negated_conjecture,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_647,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12473,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12463,c_647])).

cnf(c_24,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_894,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1162,plain,
    ( v2_compts_1(sK1,X0)
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_1261,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_1262,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_649,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_753,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_649,c_651])).

cnf(c_3212,plain,
    ( v2_compts_1(u1_struct_0(X0),X0) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_753])).

cnf(c_6599,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0) = iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4476,c_3212])).

cnf(c_6636,plain,
    ( v2_compts_1(sK1,X0) = iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6599,c_4476])).

cnf(c_6651,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6636])).

cnf(c_12563,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12473,c_18,c_19,c_24,c_40,c_812,c_832,c_836,c_874,c_913,c_1055,c_1262,c_2103,c_2284,c_2320,c_2780,c_5373,c_5505,c_6651,c_6690,c_8387,c_9413])).

cnf(c_12565,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12563])).

cnf(c_9443,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9413])).

cnf(c_648,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_741,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_648,c_651])).

cnf(c_2386,plain,
    ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_741])).

cnf(c_5787,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_compts_1(sK1,X0) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4476,c_2386])).

cnf(c_5824,plain,
    ( v2_compts_1(sK1,X0) != iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5787,c_4476])).

cnf(c_5838,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
    | ~ l1_pre_topc(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5824])).

cnf(c_5840,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_5838])).

cnf(c_17,negated_conjecture,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12675,c_12565,c_9443,c_8387,c_6689,c_5840,c_5499,c_5373,c_4476,c_2320,c_2284,c_1052,c_913,c_873,c_831,c_811,c_39,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.90/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/1.00  
% 3.90/1.00  ------  iProver source info
% 3.90/1.00  
% 3.90/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.90/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/1.00  git: non_committed_changes: false
% 3.90/1.00  git: last_make_outside_of_git: false
% 3.90/1.00  
% 3.90/1.00  ------ 
% 3.90/1.00  
% 3.90/1.00  ------ Input Options
% 3.90/1.00  
% 3.90/1.00  --out_options                           all
% 3.90/1.00  --tptp_safe_out                         true
% 3.90/1.00  --problem_path                          ""
% 3.90/1.00  --include_path                          ""
% 3.90/1.00  --clausifier                            res/vclausify_rel
% 3.90/1.00  --clausifier_options                    --mode clausify
% 3.90/1.00  --stdin                                 false
% 3.90/1.00  --stats_out                             all
% 3.90/1.00  
% 3.90/1.00  ------ General Options
% 3.90/1.00  
% 3.90/1.00  --fof                                   false
% 3.90/1.00  --time_out_real                         305.
% 3.90/1.00  --time_out_virtual                      -1.
% 3.90/1.00  --symbol_type_check                     false
% 3.90/1.00  --clausify_out                          false
% 3.90/1.00  --sig_cnt_out                           false
% 3.90/1.00  --trig_cnt_out                          false
% 3.90/1.00  --trig_cnt_out_tolerance                1.
% 3.90/1.00  --trig_cnt_out_sk_spl                   false
% 3.90/1.00  --abstr_cl_out                          false
% 3.90/1.00  
% 3.90/1.00  ------ Global Options
% 3.90/1.00  
% 3.90/1.00  --schedule                              default
% 3.90/1.00  --add_important_lit                     false
% 3.90/1.00  --prop_solver_per_cl                    1000
% 3.90/1.00  --min_unsat_core                        false
% 3.90/1.00  --soft_assumptions                      false
% 3.90/1.00  --soft_lemma_size                       3
% 3.90/1.00  --prop_impl_unit_size                   0
% 3.90/1.00  --prop_impl_unit                        []
% 3.90/1.00  --share_sel_clauses                     true
% 3.90/1.00  --reset_solvers                         false
% 3.90/1.00  --bc_imp_inh                            [conj_cone]
% 3.90/1.00  --conj_cone_tolerance                   3.
% 3.90/1.00  --extra_neg_conj                        none
% 3.90/1.00  --large_theory_mode                     true
% 3.90/1.00  --prolific_symb_bound                   200
% 3.90/1.00  --lt_threshold                          2000
% 3.90/1.00  --clause_weak_htbl                      true
% 3.90/1.00  --gc_record_bc_elim                     false
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing Options
% 3.90/1.00  
% 3.90/1.00  --preprocessing_flag                    true
% 3.90/1.00  --time_out_prep_mult                    0.1
% 3.90/1.00  --splitting_mode                        input
% 3.90/1.00  --splitting_grd                         true
% 3.90/1.00  --splitting_cvd                         false
% 3.90/1.00  --splitting_cvd_svl                     false
% 3.90/1.00  --splitting_nvd                         32
% 3.90/1.00  --sub_typing                            true
% 3.90/1.00  --prep_gs_sim                           true
% 3.90/1.00  --prep_unflatten                        true
% 3.90/1.00  --prep_res_sim                          true
% 3.90/1.00  --prep_upred                            true
% 3.90/1.00  --prep_sem_filter                       exhaustive
% 3.90/1.00  --prep_sem_filter_out                   false
% 3.90/1.00  --pred_elim                             true
% 3.90/1.00  --res_sim_input                         true
% 3.90/1.00  --eq_ax_congr_red                       true
% 3.90/1.00  --pure_diseq_elim                       true
% 3.90/1.00  --brand_transform                       false
% 3.90/1.00  --non_eq_to_eq                          false
% 3.90/1.00  --prep_def_merge                        true
% 3.90/1.00  --prep_def_merge_prop_impl              false
% 3.90/1.00  --prep_def_merge_mbd                    true
% 3.90/1.00  --prep_def_merge_tr_red                 false
% 3.90/1.00  --prep_def_merge_tr_cl                  false
% 3.90/1.00  --smt_preprocessing                     true
% 3.90/1.00  --smt_ac_axioms                         fast
% 3.90/1.00  --preprocessed_out                      false
% 3.90/1.00  --preprocessed_stats                    false
% 3.90/1.00  
% 3.90/1.00  ------ Abstraction refinement Options
% 3.90/1.00  
% 3.90/1.00  --abstr_ref                             []
% 3.90/1.00  --abstr_ref_prep                        false
% 3.90/1.00  --abstr_ref_until_sat                   false
% 3.90/1.00  --abstr_ref_sig_restrict                funpre
% 3.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/1.00  --abstr_ref_under                       []
% 3.90/1.00  
% 3.90/1.00  ------ SAT Options
% 3.90/1.00  
% 3.90/1.00  --sat_mode                              false
% 3.90/1.00  --sat_fm_restart_options                ""
% 3.90/1.00  --sat_gr_def                            false
% 3.90/1.00  --sat_epr_types                         true
% 3.90/1.00  --sat_non_cyclic_types                  false
% 3.90/1.00  --sat_finite_models                     false
% 3.90/1.00  --sat_fm_lemmas                         false
% 3.90/1.00  --sat_fm_prep                           false
% 3.90/1.00  --sat_fm_uc_incr                        true
% 3.90/1.00  --sat_out_model                         small
% 3.90/1.00  --sat_out_clauses                       false
% 3.90/1.00  
% 3.90/1.00  ------ QBF Options
% 3.90/1.00  
% 3.90/1.00  --qbf_mode                              false
% 3.90/1.00  --qbf_elim_univ                         false
% 3.90/1.00  --qbf_dom_inst                          none
% 3.90/1.00  --qbf_dom_pre_inst                      false
% 3.90/1.00  --qbf_sk_in                             false
% 3.90/1.00  --qbf_pred_elim                         true
% 3.90/1.00  --qbf_split                             512
% 3.90/1.00  
% 3.90/1.00  ------ BMC1 Options
% 3.90/1.00  
% 3.90/1.00  --bmc1_incremental                      false
% 3.90/1.00  --bmc1_axioms                           reachable_all
% 3.90/1.00  --bmc1_min_bound                        0
% 3.90/1.00  --bmc1_max_bound                        -1
% 3.90/1.00  --bmc1_max_bound_default                -1
% 3.90/1.00  --bmc1_symbol_reachability              true
% 3.90/1.00  --bmc1_property_lemmas                  false
% 3.90/1.00  --bmc1_k_induction                      false
% 3.90/1.00  --bmc1_non_equiv_states                 false
% 3.90/1.00  --bmc1_deadlock                         false
% 3.90/1.00  --bmc1_ucm                              false
% 3.90/1.00  --bmc1_add_unsat_core                   none
% 3.90/1.00  --bmc1_unsat_core_children              false
% 3.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/1.00  --bmc1_out_stat                         full
% 3.90/1.00  --bmc1_ground_init                      false
% 3.90/1.00  --bmc1_pre_inst_next_state              false
% 3.90/1.00  --bmc1_pre_inst_state                   false
% 3.90/1.00  --bmc1_pre_inst_reach_state             false
% 3.90/1.00  --bmc1_out_unsat_core                   false
% 3.90/1.00  --bmc1_aig_witness_out                  false
% 3.90/1.00  --bmc1_verbose                          false
% 3.90/1.00  --bmc1_dump_clauses_tptp                false
% 3.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.90/1.00  --bmc1_dump_file                        -
% 3.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.90/1.00  --bmc1_ucm_extend_mode                  1
% 3.90/1.00  --bmc1_ucm_init_mode                    2
% 3.90/1.00  --bmc1_ucm_cone_mode                    none
% 3.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.90/1.00  --bmc1_ucm_relax_model                  4
% 3.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/1.00  --bmc1_ucm_layered_model                none
% 3.90/1.00  --bmc1_ucm_max_lemma_size               10
% 3.90/1.00  
% 3.90/1.00  ------ AIG Options
% 3.90/1.00  
% 3.90/1.00  --aig_mode                              false
% 3.90/1.00  
% 3.90/1.00  ------ Instantiation Options
% 3.90/1.00  
% 3.90/1.00  --instantiation_flag                    true
% 3.90/1.00  --inst_sos_flag                         false
% 3.90/1.00  --inst_sos_phase                        true
% 3.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel_side                     num_symb
% 3.90/1.00  --inst_solver_per_active                1400
% 3.90/1.00  --inst_solver_calls_frac                1.
% 3.90/1.00  --inst_passive_queue_type               priority_queues
% 3.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/1.00  --inst_passive_queues_freq              [25;2]
% 3.90/1.00  --inst_dismatching                      true
% 3.90/1.00  --inst_eager_unprocessed_to_passive     true
% 3.90/1.00  --inst_prop_sim_given                   true
% 3.90/1.00  --inst_prop_sim_new                     false
% 3.90/1.00  --inst_subs_new                         false
% 3.90/1.00  --inst_eq_res_simp                      false
% 3.90/1.00  --inst_subs_given                       false
% 3.90/1.00  --inst_orphan_elimination               true
% 3.90/1.00  --inst_learning_loop_flag               true
% 3.90/1.00  --inst_learning_start                   3000
% 3.90/1.00  --inst_learning_factor                  2
% 3.90/1.00  --inst_start_prop_sim_after_learn       3
% 3.90/1.00  --inst_sel_renew                        solver
% 3.90/1.00  --inst_lit_activity_flag                true
% 3.90/1.00  --inst_restr_to_given                   false
% 3.90/1.00  --inst_activity_threshold               500
% 3.90/1.00  --inst_out_proof                        true
% 3.90/1.00  
% 3.90/1.00  ------ Resolution Options
% 3.90/1.00  
% 3.90/1.00  --resolution_flag                       true
% 3.90/1.00  --res_lit_sel                           adaptive
% 3.90/1.00  --res_lit_sel_side                      none
% 3.90/1.00  --res_ordering                          kbo
% 3.90/1.00  --res_to_prop_solver                    active
% 3.90/1.00  --res_prop_simpl_new                    false
% 3.90/1.00  --res_prop_simpl_given                  true
% 3.90/1.00  --res_passive_queue_type                priority_queues
% 3.90/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/1.00  --res_passive_queues_freq               [15;5]
% 3.90/1.00  --res_forward_subs                      full
% 3.90/1.00  --res_backward_subs                     full
% 3.90/1.00  --res_forward_subs_resolution           true
% 3.90/1.00  --res_backward_subs_resolution          true
% 3.90/1.00  --res_orphan_elimination                true
% 3.90/1.00  --res_time_limit                        2.
% 3.90/1.00  --res_out_proof                         true
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Options
% 3.90/1.00  
% 3.90/1.00  --superposition_flag                    true
% 3.90/1.00  --sup_passive_queue_type                priority_queues
% 3.90/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.90/1.00  --demod_completeness_check              fast
% 3.90/1.00  --demod_use_ground                      true
% 3.90/1.00  --sup_to_prop_solver                    passive
% 3.90/1.00  --sup_prop_simpl_new                    true
% 3.90/1.00  --sup_prop_simpl_given                  true
% 3.90/1.00  --sup_fun_splitting                     false
% 3.90/1.00  --sup_smt_interval                      50000
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Simplification Setup
% 3.90/1.00  
% 3.90/1.00  --sup_indices_passive                   []
% 3.90/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_full_bw                           [BwDemod]
% 3.90/1.00  --sup_immed_triv                        [TrivRules]
% 3.90/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_immed_bw_main                     []
% 3.90/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  
% 3.90/1.00  ------ Combination Options
% 3.90/1.00  
% 3.90/1.00  --comb_res_mult                         3
% 3.90/1.00  --comb_sup_mult                         2
% 3.90/1.00  --comb_inst_mult                        10
% 3.90/1.00  
% 3.90/1.00  ------ Debug Options
% 3.90/1.00  
% 3.90/1.00  --dbg_backtrace                         false
% 3.90/1.00  --dbg_dump_prop_clauses                 false
% 3.90/1.00  --dbg_dump_prop_clauses_file            -
% 3.90/1.00  --dbg_out_stat                          false
% 3.90/1.00  ------ Parsing...
% 3.90/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/1.00  ------ Proving...
% 3.90/1.00  ------ Problem Properties 
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  clauses                                 18
% 3.90/1.00  conjectures                             6
% 3.90/1.00  EPR                                     2
% 3.90/1.00  Horn                                    14
% 3.90/1.00  unary                                   3
% 3.90/1.00  binary                                  6
% 3.90/1.00  lits                                    50
% 3.90/1.00  lits eq                                 2
% 3.90/1.00  fd_pure                                 0
% 3.90/1.00  fd_pseudo                               0
% 3.90/1.00  fd_cond                                 0
% 3.90/1.00  fd_pseudo_cond                          0
% 3.90/1.00  AC symbols                              0
% 3.90/1.00  
% 3.90/1.00  ------ Schedule dynamic 5 is on 
% 3.90/1.00  
% 3.90/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  ------ 
% 3.90/1.00  Current options:
% 3.90/1.00  ------ 
% 3.90/1.00  
% 3.90/1.00  ------ Input Options
% 3.90/1.00  
% 3.90/1.00  --out_options                           all
% 3.90/1.00  --tptp_safe_out                         true
% 3.90/1.00  --problem_path                          ""
% 3.90/1.00  --include_path                          ""
% 3.90/1.00  --clausifier                            res/vclausify_rel
% 3.90/1.00  --clausifier_options                    --mode clausify
% 3.90/1.00  --stdin                                 false
% 3.90/1.00  --stats_out                             all
% 3.90/1.00  
% 3.90/1.00  ------ General Options
% 3.90/1.00  
% 3.90/1.00  --fof                                   false
% 3.90/1.00  --time_out_real                         305.
% 3.90/1.00  --time_out_virtual                      -1.
% 3.90/1.00  --symbol_type_check                     false
% 3.90/1.00  --clausify_out                          false
% 3.90/1.00  --sig_cnt_out                           false
% 3.90/1.00  --trig_cnt_out                          false
% 3.90/1.00  --trig_cnt_out_tolerance                1.
% 3.90/1.00  --trig_cnt_out_sk_spl                   false
% 3.90/1.00  --abstr_cl_out                          false
% 3.90/1.00  
% 3.90/1.00  ------ Global Options
% 3.90/1.00  
% 3.90/1.00  --schedule                              default
% 3.90/1.00  --add_important_lit                     false
% 3.90/1.00  --prop_solver_per_cl                    1000
% 3.90/1.00  --min_unsat_core                        false
% 3.90/1.00  --soft_assumptions                      false
% 3.90/1.00  --soft_lemma_size                       3
% 3.90/1.00  --prop_impl_unit_size                   0
% 3.90/1.00  --prop_impl_unit                        []
% 3.90/1.00  --share_sel_clauses                     true
% 3.90/1.00  --reset_solvers                         false
% 3.90/1.00  --bc_imp_inh                            [conj_cone]
% 3.90/1.00  --conj_cone_tolerance                   3.
% 3.90/1.00  --extra_neg_conj                        none
% 3.90/1.00  --large_theory_mode                     true
% 3.90/1.00  --prolific_symb_bound                   200
% 3.90/1.00  --lt_threshold                          2000
% 3.90/1.00  --clause_weak_htbl                      true
% 3.90/1.00  --gc_record_bc_elim                     false
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing Options
% 3.90/1.00  
% 3.90/1.00  --preprocessing_flag                    true
% 3.90/1.00  --time_out_prep_mult                    0.1
% 3.90/1.00  --splitting_mode                        input
% 3.90/1.00  --splitting_grd                         true
% 3.90/1.00  --splitting_cvd                         false
% 3.90/1.00  --splitting_cvd_svl                     false
% 3.90/1.00  --splitting_nvd                         32
% 3.90/1.00  --sub_typing                            true
% 3.90/1.00  --prep_gs_sim                           true
% 3.90/1.00  --prep_unflatten                        true
% 3.90/1.00  --prep_res_sim                          true
% 3.90/1.00  --prep_upred                            true
% 3.90/1.00  --prep_sem_filter                       exhaustive
% 3.90/1.00  --prep_sem_filter_out                   false
% 3.90/1.00  --pred_elim                             true
% 3.90/1.00  --res_sim_input                         true
% 3.90/1.00  --eq_ax_congr_red                       true
% 3.90/1.00  --pure_diseq_elim                       true
% 3.90/1.00  --brand_transform                       false
% 3.90/1.00  --non_eq_to_eq                          false
% 3.90/1.00  --prep_def_merge                        true
% 3.90/1.00  --prep_def_merge_prop_impl              false
% 3.90/1.00  --prep_def_merge_mbd                    true
% 3.90/1.00  --prep_def_merge_tr_red                 false
% 3.90/1.00  --prep_def_merge_tr_cl                  false
% 3.90/1.00  --smt_preprocessing                     true
% 3.90/1.00  --smt_ac_axioms                         fast
% 3.90/1.00  --preprocessed_out                      false
% 3.90/1.00  --preprocessed_stats                    false
% 3.90/1.00  
% 3.90/1.00  ------ Abstraction refinement Options
% 3.90/1.00  
% 3.90/1.00  --abstr_ref                             []
% 3.90/1.00  --abstr_ref_prep                        false
% 3.90/1.00  --abstr_ref_until_sat                   false
% 3.90/1.00  --abstr_ref_sig_restrict                funpre
% 3.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/1.00  --abstr_ref_under                       []
% 3.90/1.00  
% 3.90/1.00  ------ SAT Options
% 3.90/1.00  
% 3.90/1.00  --sat_mode                              false
% 3.90/1.00  --sat_fm_restart_options                ""
% 3.90/1.00  --sat_gr_def                            false
% 3.90/1.00  --sat_epr_types                         true
% 3.90/1.00  --sat_non_cyclic_types                  false
% 3.90/1.00  --sat_finite_models                     false
% 3.90/1.00  --sat_fm_lemmas                         false
% 3.90/1.00  --sat_fm_prep                           false
% 3.90/1.00  --sat_fm_uc_incr                        true
% 3.90/1.00  --sat_out_model                         small
% 3.90/1.00  --sat_out_clauses                       false
% 3.90/1.00  
% 3.90/1.00  ------ QBF Options
% 3.90/1.00  
% 3.90/1.00  --qbf_mode                              false
% 3.90/1.00  --qbf_elim_univ                         false
% 3.90/1.00  --qbf_dom_inst                          none
% 3.90/1.00  --qbf_dom_pre_inst                      false
% 3.90/1.00  --qbf_sk_in                             false
% 3.90/1.00  --qbf_pred_elim                         true
% 3.90/1.00  --qbf_split                             512
% 3.90/1.00  
% 3.90/1.00  ------ BMC1 Options
% 3.90/1.00  
% 3.90/1.00  --bmc1_incremental                      false
% 3.90/1.00  --bmc1_axioms                           reachable_all
% 3.90/1.00  --bmc1_min_bound                        0
% 3.90/1.00  --bmc1_max_bound                        -1
% 3.90/1.00  --bmc1_max_bound_default                -1
% 3.90/1.00  --bmc1_symbol_reachability              true
% 3.90/1.00  --bmc1_property_lemmas                  false
% 3.90/1.00  --bmc1_k_induction                      false
% 3.90/1.00  --bmc1_non_equiv_states                 false
% 3.90/1.00  --bmc1_deadlock                         false
% 3.90/1.00  --bmc1_ucm                              false
% 3.90/1.00  --bmc1_add_unsat_core                   none
% 3.90/1.00  --bmc1_unsat_core_children              false
% 3.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/1.00  --bmc1_out_stat                         full
% 3.90/1.00  --bmc1_ground_init                      false
% 3.90/1.00  --bmc1_pre_inst_next_state              false
% 3.90/1.00  --bmc1_pre_inst_state                   false
% 3.90/1.00  --bmc1_pre_inst_reach_state             false
% 3.90/1.00  --bmc1_out_unsat_core                   false
% 3.90/1.00  --bmc1_aig_witness_out                  false
% 3.90/1.00  --bmc1_verbose                          false
% 3.90/1.00  --bmc1_dump_clauses_tptp                false
% 3.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.90/1.00  --bmc1_dump_file                        -
% 3.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.90/1.00  --bmc1_ucm_extend_mode                  1
% 3.90/1.00  --bmc1_ucm_init_mode                    2
% 3.90/1.00  --bmc1_ucm_cone_mode                    none
% 3.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.90/1.00  --bmc1_ucm_relax_model                  4
% 3.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/1.00  --bmc1_ucm_layered_model                none
% 3.90/1.00  --bmc1_ucm_max_lemma_size               10
% 3.90/1.00  
% 3.90/1.00  ------ AIG Options
% 3.90/1.00  
% 3.90/1.00  --aig_mode                              false
% 3.90/1.00  
% 3.90/1.00  ------ Instantiation Options
% 3.90/1.00  
% 3.90/1.00  --instantiation_flag                    true
% 3.90/1.00  --inst_sos_flag                         false
% 3.90/1.00  --inst_sos_phase                        true
% 3.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel_side                     none
% 3.90/1.00  --inst_solver_per_active                1400
% 3.90/1.00  --inst_solver_calls_frac                1.
% 3.90/1.00  --inst_passive_queue_type               priority_queues
% 3.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/1.00  --inst_passive_queues_freq              [25;2]
% 3.90/1.00  --inst_dismatching                      true
% 3.90/1.00  --inst_eager_unprocessed_to_passive     true
% 3.90/1.00  --inst_prop_sim_given                   true
% 3.90/1.00  --inst_prop_sim_new                     false
% 3.90/1.00  --inst_subs_new                         false
% 3.90/1.00  --inst_eq_res_simp                      false
% 3.90/1.00  --inst_subs_given                       false
% 3.90/1.00  --inst_orphan_elimination               true
% 3.90/1.00  --inst_learning_loop_flag               true
% 3.90/1.00  --inst_learning_start                   3000
% 3.90/1.00  --inst_learning_factor                  2
% 3.90/1.00  --inst_start_prop_sim_after_learn       3
% 3.90/1.00  --inst_sel_renew                        solver
% 3.90/1.00  --inst_lit_activity_flag                true
% 3.90/1.00  --inst_restr_to_given                   false
% 3.90/1.00  --inst_activity_threshold               500
% 3.90/1.00  --inst_out_proof                        true
% 3.90/1.00  
% 3.90/1.00  ------ Resolution Options
% 3.90/1.00  
% 3.90/1.00  --resolution_flag                       false
% 3.90/1.00  --res_lit_sel                           adaptive
% 3.90/1.00  --res_lit_sel_side                      none
% 3.90/1.00  --res_ordering                          kbo
% 3.90/1.00  --res_to_prop_solver                    active
% 3.90/1.00  --res_prop_simpl_new                    false
% 3.90/1.00  --res_prop_simpl_given                  true
% 3.90/1.00  --res_passive_queue_type                priority_queues
% 3.90/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/1.00  --res_passive_queues_freq               [15;5]
% 3.90/1.00  --res_forward_subs                      full
% 3.90/1.00  --res_backward_subs                     full
% 3.90/1.00  --res_forward_subs_resolution           true
% 3.90/1.00  --res_backward_subs_resolution          true
% 3.90/1.00  --res_orphan_elimination                true
% 3.90/1.00  --res_time_limit                        2.
% 3.90/1.00  --res_out_proof                         true
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Options
% 3.90/1.00  
% 3.90/1.00  --superposition_flag                    true
% 3.90/1.00  --sup_passive_queue_type                priority_queues
% 3.90/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.90/1.00  --demod_completeness_check              fast
% 3.90/1.00  --demod_use_ground                      true
% 3.90/1.00  --sup_to_prop_solver                    passive
% 3.90/1.00  --sup_prop_simpl_new                    true
% 3.90/1.00  --sup_prop_simpl_given                  true
% 3.90/1.00  --sup_fun_splitting                     false
% 3.90/1.00  --sup_smt_interval                      50000
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Simplification Setup
% 3.90/1.00  
% 3.90/1.00  --sup_indices_passive                   []
% 3.90/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_full_bw                           [BwDemod]
% 3.90/1.00  --sup_immed_triv                        [TrivRules]
% 3.90/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_immed_bw_main                     []
% 3.90/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  
% 3.90/1.00  ------ Combination Options
% 3.90/1.00  
% 3.90/1.00  --comb_res_mult                         3
% 3.90/1.00  --comb_sup_mult                         2
% 3.90/1.00  --comb_inst_mult                        10
% 3.90/1.00  
% 3.90/1.00  ------ Debug Options
% 3.90/1.00  
% 3.90/1.00  --dbg_backtrace                         false
% 3.90/1.00  --dbg_dump_prop_clauses                 false
% 3.90/1.00  --dbg_dump_prop_clauses_file            -
% 3.90/1.00  --dbg_out_stat                          false
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  ------ Proving...
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  % SZS status Theorem for theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  fof(f11,axiom,(
% 3.90/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f27,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f11])).
% 3.90/1.00  
% 3.90/1.00  fof(f28,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(flattening,[],[f27])).
% 3.90/1.00  
% 3.90/1.00  fof(f31,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(nnf_transformation,[],[f28])).
% 3.90/1.00  
% 3.90/1.00  fof(f49,plain,(
% 3.90/1.00    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f31])).
% 3.90/1.00  
% 3.90/1.00  fof(f56,plain,(
% 3.90/1.00    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(equality_resolution,[],[f49])).
% 3.90/1.00  
% 3.90/1.00  fof(f12,conjecture,(
% 3.90/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f13,negated_conjecture,(
% 3.90/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.90/1.00    inference(negated_conjecture,[],[f12])).
% 3.90/1.00  
% 3.90/1.00  fof(f14,plain,(
% 3.90/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.90/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.90/1.00  
% 3.90/1.00  fof(f15,plain,(
% 3.90/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.90/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.90/1.00  
% 3.90/1.00  fof(f29,plain,(
% 3.90/1.00    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f15])).
% 3.90/1.00  
% 3.90/1.00  fof(f32,plain,(
% 3.90/1.00    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 3.90/1.00    inference(nnf_transformation,[],[f29])).
% 3.90/1.00  
% 3.90/1.00  fof(f33,plain,(
% 3.90/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 3.90/1.00    inference(flattening,[],[f32])).
% 3.90/1.00  
% 3.90/1.00  fof(f35,plain,(
% 3.90/1.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(sK1,X0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(sK1,X0))))) )),
% 3.90/1.00    introduced(choice_axiom,[])).
% 3.90/1.00  
% 3.90/1.00  fof(f34,plain,(
% 3.90/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0))),
% 3.90/1.00    introduced(choice_axiom,[])).
% 3.90/1.00  
% 3.90/1.00  fof(f36,plain,(
% 3.90/1.00    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0)),
% 3.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 3.90/1.00  
% 3.90/1.00  fof(f50,plain,(
% 3.90/1.00    l1_pre_topc(sK0)),
% 3.90/1.00    inference(cnf_transformation,[],[f36])).
% 3.90/1.00  
% 3.90/1.00  fof(f6,axiom,(
% 3.90/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f22,plain,(
% 3.90/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f6])).
% 3.90/1.00  
% 3.90/1.00  fof(f42,plain,(
% 3.90/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f22])).
% 3.90/1.00  
% 3.90/1.00  fof(f3,axiom,(
% 3.90/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f17,plain,(
% 3.90/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.90/1.00    inference(pure_predicate_removal,[],[f3])).
% 3.90/1.00  
% 3.90/1.00  fof(f18,plain,(
% 3.90/1.00    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.90/1.00    inference(ennf_transformation,[],[f17])).
% 3.90/1.00  
% 3.90/1.00  fof(f39,plain,(
% 3.90/1.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.90/1.00    inference(cnf_transformation,[],[f18])).
% 3.90/1.00  
% 3.90/1.00  fof(f2,axiom,(
% 3.90/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f38,plain,(
% 3.90/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.90/1.00    inference(cnf_transformation,[],[f2])).
% 3.90/1.00  
% 3.90/1.00  fof(f1,axiom,(
% 3.90/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f37,plain,(
% 3.90/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.90/1.00    inference(cnf_transformation,[],[f1])).
% 3.90/1.00  
% 3.90/1.00  fof(f7,axiom,(
% 3.90/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f23,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f7])).
% 3.90/1.00  
% 3.90/1.00  fof(f43,plain,(
% 3.90/1.00    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f23])).
% 3.90/1.00  
% 3.90/1.00  fof(f54,plain,(
% 3.90/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.90/1.00    inference(cnf_transformation,[],[f36])).
% 3.90/1.00  
% 3.90/1.00  fof(f4,axiom,(
% 3.90/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f16,plain,(
% 3.90/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 3.90/1.00    inference(pure_predicate_removal,[],[f4])).
% 3.90/1.00  
% 3.90/1.00  fof(f19,plain,(
% 3.90/1.00    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.90/1.00    inference(ennf_transformation,[],[f16])).
% 3.90/1.00  
% 3.90/1.00  fof(f20,plain,(
% 3.90/1.00    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(flattening,[],[f19])).
% 3.90/1.00  
% 3.90/1.00  fof(f40,plain,(
% 3.90/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f20])).
% 3.90/1.00  
% 3.90/1.00  fof(f9,axiom,(
% 3.90/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f25,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f9])).
% 3.90/1.00  
% 3.90/1.00  fof(f45,plain,(
% 3.90/1.00    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f25])).
% 3.90/1.00  
% 3.90/1.00  fof(f8,axiom,(
% 3.90/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f24,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f8])).
% 3.90/1.00  
% 3.90/1.00  fof(f44,plain,(
% 3.90/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f24])).
% 3.90/1.00  
% 3.90/1.00  fof(f5,axiom,(
% 3.90/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f21,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f5])).
% 3.90/1.00  
% 3.90/1.00  fof(f41,plain,(
% 3.90/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f21])).
% 3.90/1.00  
% 3.90/1.00  fof(f10,axiom,(
% 3.90/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f26,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(ennf_transformation,[],[f10])).
% 3.90/1.00  
% 3.90/1.00  fof(f30,plain,(
% 3.90/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.90/1.00    inference(nnf_transformation,[],[f26])).
% 3.90/1.00  
% 3.90/1.00  fof(f46,plain,(
% 3.90/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f30])).
% 3.90/1.00  
% 3.90/1.00  fof(f55,plain,(
% 3.90/1.00    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 3.90/1.00    inference(cnf_transformation,[],[f36])).
% 3.90/1.00  
% 3.90/1.00  fof(f48,plain,(
% 3.90/1.00    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f31])).
% 3.90/1.00  
% 3.90/1.00  fof(f57,plain,(
% 3.90/1.00    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/1.00    inference(equality_resolution,[],[f48])).
% 3.90/1.00  
% 3.90/1.00  fof(f51,plain,(
% 3.90/1.00    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 3.90/1.00    inference(cnf_transformation,[],[f36])).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11,plain,
% 3.90/1.00      ( ~ v2_compts_1(X0,X1)
% 3.90/1.00      | v2_compts_1(X0,X2)
% 3.90/1.00      | ~ m1_pre_topc(X1,X2)
% 3.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.90/1.00      | ~ l1_pre_topc(X2) ),
% 3.90/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_895,plain,
% 3.90/1.00      ( ~ v2_compts_1(sK1,X0)
% 3.90/1.00      | v2_compts_1(sK1,X1)
% 3.90/1.00      | ~ m1_pre_topc(X0,X1)
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X1) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12103,plain,
% 3.90/1.00      ( ~ v2_compts_1(sK1,X0)
% 3.90/1.00      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_895]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12675,plain,
% 3.90/1.00      ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 3.90/1.00      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_12103]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_18,negated_conjecture,
% 3.90/1.00      ( l1_pre_topc(sK0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_642,plain,
% 3.90/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5,plain,
% 3.90/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.90/1.00      | ~ l1_pre_topc(X0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_653,plain,
% 3.90/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2,plain,
% 3.90/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.90/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_656,plain,
% 3.90/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1146,plain,
% 3.90/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_653,c_656]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1,plain,
% 3.90/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.90/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_657,plain,
% 3.90/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_0,plain,
% 3.90/1.00      ( k2_subset_1(X0) = X0 ),
% 3.90/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_662,plain,
% 3.90/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_657,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6,plain,
% 3.90/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X1)
% 3.90/1.00      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.90/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_652,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 3.90/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1350,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_662,c_652]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1772,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) = u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1146,c_1350]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_10212,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_642,c_1772]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_14,negated_conjecture,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.90/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_646,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.90/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/1.00      | ~ l1_pre_topc(X0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_655,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 3.90/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1562,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_646,c_655]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_19,plain,
% 3.90/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_38,plain,
% 3.90/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_40,plain,
% 3.90/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_38]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_809,plain,
% 3.90/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_810,plain,
% 3.90/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_812,plain,
% 3.90/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_810]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2082,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_1562,c_19,c_40,c_812]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2083,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_2082]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8,plain,
% 3.90/1.00      ( m1_pre_topc(X0,X1)
% 3.90/1.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_650,plain,
% 3.90/1.00      ( m1_pre_topc(X0,X1) = iProver_top
% 3.90/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2089,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2083,c_650]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4293,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_2089,c_19]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4294,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_4293]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1348,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_646,c_652]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1409,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_1348,c_19,c_40,c_812]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1410,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_1409]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1771,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_642,c_1350]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1796,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0),k1_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/1.00      | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1771,c_655]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7,plain,
% 3.90/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.90/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_651,plain,
% 3.90/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.90/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1614,plain,
% 3.90/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.90/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_662,c_651]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2692,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) = u1_struct_0(X1)
% 3.90/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1614,c_652]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3582,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0))
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/1.00      | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1796,c_2692]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1565,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_662,c_655]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4,plain,
% 3.90/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_654,plain,
% 3.90/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2441,plain,
% 3.90/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.90/1.00      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1565,c_654]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2466,plain,
% 3.90/1.00      ( l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_2441]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8478,plain,
% 3.90/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/1.00      | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)) ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_3582,c_19,c_2466]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8479,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X0))
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_8478]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8487,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK1)))) = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK1))
% 3.90/1.00      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1410,c_8479]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_39,plain,
% 3.90/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.90/1.00      | ~ l1_pre_topc(sK0) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_811,plain,
% 3.90/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_809]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_10,plain,
% 3.90/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.90/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X0)
% 3.90/1.00      | ~ l1_pre_topc(X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_97,plain,
% 3.90/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.90/1.00      | ~ m1_pre_topc(X0,X1)
% 3.90/1.00      | ~ l1_pre_topc(X1) ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_10,c_4]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_98,plain,
% 3.90/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.90/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X1) ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_97]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_873,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 3.90/1.00      | ~ l1_pre_topc(sK0) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_98]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_319,plain,( X0 = X0 ),theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_913,plain,
% 3.90/1.00      ( sK1 = sK1 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_319]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1004,plain,
% 3.90/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_822,plain,
% 3.90/1.00      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1052,plain,
% 3.90/1.00      ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_822]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_320,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1136,plain,
% 3.90/1.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_320]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1871,plain,
% 3.90/1.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1136]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2284,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1
% 3.90/1.00      | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
% 3.90/1.00      | sK1 != sK1 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1871]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2320,plain,
% 3.90/1.00      ( k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1564,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1410,c_655]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4178,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.90/1.00      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_1564,c_19]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4179,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_4178]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4180,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 3.90/1.00      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 3.90/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4179]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1415,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 3.90/1.00      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1410,c_652]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1418,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 3.90/1.00      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_1415,c_19]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1419,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 3.90/1.00      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_1418]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1422,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)) = X0
% 3.90/1.00      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.90/1.00      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1419,c_652]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_836,plain,
% 3.90/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.00      | ~ l1_pre_topc(sK0)
% 3.90/1.00      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2103,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.00      | ~ l1_pre_topc(sK0) ),
% 3.90/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2089]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2685,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1419,c_1614]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2778,plain,
% 3.90/1.00      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/1.00      | ~ l1_pre_topc(X0)
% 3.90/1.00      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 3.90/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2685]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2780,plain,
% 3.90/1.00      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.00      | ~ l1_pre_topc(sK0)
% 3.90/1.00      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_2778]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4476,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_1422,c_18,c_836,c_2103,c_2780]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2825,plain,
% 3.90/1.00      ( X0 != u1_struct_0(k1_pre_topc(sK0,sK1))
% 3.90/1.00      | sK1 = X0
% 3.90/1.00      | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1136]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5373,plain,
% 3.90/1.00      ( k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != u1_struct_0(k1_pre_topc(sK0,sK1))
% 3.90/1.00      | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1))
% 3.90/1.00      | sK1 = k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_2825]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1019,plain,
% 3.90/1.00      ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5499,plain,
% 3.90/1.00      ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1019]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_322,plain,
% 3.90/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.90/1.00      theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_839,plain,
% 3.90/1.00      ( m1_subset_1(X0,X1)
% 3.90/1.00      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 3.90/1.00      | X1 != k1_zfmisc_1(X2)
% 3.90/1.00      | X0 != k2_subset_1(X2) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_322]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1087,plain,
% 3.90/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/1.00      | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
% 3.90/1.00      | X0 != k2_subset_1(X1)
% 3.90/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_839]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1948,plain,
% 3.90/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | ~ m1_subset_1(k2_subset_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | X0 != k2_subset_1(u1_struct_0(X1))
% 3.90/1.00      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1087]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6689,plain,
% 3.90/1.00      ( ~ m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 3.90/1.00      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
% 3.90/1.00      | sK1 != k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1948]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1088,plain,
% 3.90/1.00      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_319]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8387,plain,
% 3.90/1.00      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1088]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8587,plain,
% 3.90/1.00      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_8487,c_18,c_39,c_811,c_836,c_873,c_913,c_1004,c_1052,
% 3.90/1.00                 c_2103,c_2284,c_2320,c_2780,c_4180,c_5373,c_5499,c_6689,
% 3.90/1.00                 c_8387]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8603,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_8587,c_1614]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9413,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_4294,c_8603]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9446,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_9413,c_19]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9454,plain,
% 3.90/1.00      ( m1_pre_topc(sK0,X0) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_9446,c_651]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_10780,plain,
% 3.90/1.00      ( m1_pre_topc(sK0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 3.90/1.00      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_10212,c_9454]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_831,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.00      | ~ l1_pre_topc(sK0) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_832,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_874,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1055,plain,
% 3.90/1.00      ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5505,plain,
% 3.90/1.00      ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_5499]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6690,plain,
% 3.90/1.00      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
% 3.90/1.00      | sK1 != k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
% 3.90/1.00      | m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_6689]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12463,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_10780,c_18,c_19,c_40,c_812,c_832,c_836,c_874,c_913,
% 3.90/1.00                 c_1055,c_2103,c_2284,c_2320,c_2780,c_5373,c_5505,c_6690,
% 3.90/1.00                 c_8387,c_9413]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13,negated_conjecture,
% 3.90/1.00      ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ v2_compts_1(sK1,sK0)
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.90/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_647,plain,
% 3.90/1.00      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.90/1.00      | v2_compts_1(sK1,sK0) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12473,plain,
% 3.90/1.00      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.90/1.00      | v2_compts_1(sK1,sK0) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_12463,c_647]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_24,plain,
% 3.90/1.00      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.90/1.00      | v2_compts_1(sK1,sK0) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12,plain,
% 3.90/1.00      ( ~ v2_compts_1(X0,X1)
% 3.90/1.00      | v2_compts_1(X0,X2)
% 3.90/1.00      | ~ m1_pre_topc(X2,X1)
% 3.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_894,plain,
% 3.90/1.00      ( ~ v2_compts_1(sK1,X0)
% 3.90/1.00      | v2_compts_1(sK1,X1)
% 3.90/1.00      | ~ m1_pre_topc(X1,X0)
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.00      | ~ l1_pre_topc(X0) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1162,plain,
% 3.90/1.00      ( v2_compts_1(sK1,X0)
% 3.90/1.00      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_894]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1261,plain,
% 3.90/1.00      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 3.90/1.00      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 3.90/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.90/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1162]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1262,plain,
% 3.90/1.00      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
% 3.90/1.00      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
% 3.90/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 3.90/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_649,plain,
% 3.90/1.00      ( v2_compts_1(X0,X1) != iProver_top
% 3.90/1.00      | v2_compts_1(X0,X2) = iProver_top
% 3.90/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.90/1.00      | l1_pre_topc(X2) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_753,plain,
% 3.90/1.00      ( v2_compts_1(X0,X1) != iProver_top
% 3.90/1.00      | v2_compts_1(X0,X2) = iProver_top
% 3.90/1.00      | m1_pre_topc(X1,X2) != iProver_top
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.90/1.00      | l1_pre_topc(X2) != iProver_top ),
% 3.90/1.00      inference(forward_subsumption_resolution,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_649,c_651]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3212,plain,
% 3.90/1.00      ( v2_compts_1(u1_struct_0(X0),X0) != iProver_top
% 3.90/1.00      | v2_compts_1(u1_struct_0(X0),X1) = iProver_top
% 3.90/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_662,c_753]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6599,plain,
% 3.90/1.00      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0) = iProver_top
% 3.90/1.00      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_4476,c_3212]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6636,plain,
% 3.90/1.00      ( v2_compts_1(sK1,X0) = iProver_top
% 3.90/1.00      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_6599,c_4476]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6651,plain,
% 3.90/1.00      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
% 3.90/1.00      | v2_compts_1(sK1,sK0) = iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
% 3.90/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_6636]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12563,plain,
% 3.90/1.00      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_12473,c_18,c_19,c_24,c_40,c_812,c_832,c_836,c_874,
% 3.90/1.00                 c_913,c_1055,c_1262,c_2103,c_2284,c_2320,c_2780,c_5373,
% 3.90/1.00                 c_5505,c_6651,c_6690,c_8387,c_9413]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12565,plain,
% 3.90/1.00      ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.90/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_12563]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9443,plain,
% 3.90/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.00      | ~ l1_pre_topc(sK0) ),
% 3.90/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9413]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_648,plain,
% 3.90/1.00      ( v2_compts_1(X0,X1) != iProver_top
% 3.90/1.00      | v2_compts_1(X0,X2) = iProver_top
% 3.90/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_741,plain,
% 3.90/1.00      ( v2_compts_1(X0,X1) != iProver_top
% 3.90/1.00      | v2_compts_1(X0,X2) = iProver_top
% 3.90/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.90/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.00      inference(forward_subsumption_resolution,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_648,c_651]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2386,plain,
% 3.90/1.00      ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
% 3.90/1.00      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 3.90/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 3.90/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_662,c_741]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5787,plain,
% 3.90/1.00      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1)) = iProver_top
% 3.90/1.00      | v2_compts_1(sK1,X0) != iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_4476,c_2386]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5824,plain,
% 3.90/1.00      ( v2_compts_1(sK1,X0) != iProver_top
% 3.90/1.00      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
% 3.90/1.00      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 3.90/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_5787,c_4476]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5838,plain,
% 3.90/1.00      ( ~ v2_compts_1(sK1,X0)
% 3.90/1.00      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 3.90/1.00      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
% 3.90/1.00      | ~ l1_pre_topc(X0) ),
% 3.90/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5824]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5840,plain,
% 3.90/1.00      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 3.90/1.00      | ~ v2_compts_1(sK1,sK0)
% 3.90/1.00      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 3.90/1.00      | ~ l1_pre_topc(sK0) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_5838]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_17,negated_conjecture,
% 3.90/1.00      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.90/1.00      | v2_compts_1(sK1,sK0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(contradiction,plain,
% 3.90/1.00      ( $false ),
% 3.90/1.00      inference(minisat,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_12675,c_12565,c_9443,c_8387,c_6689,c_5840,c_5499,
% 3.90/1.00                 c_5373,c_4476,c_2320,c_2284,c_1052,c_913,c_873,c_831,
% 3.90/1.00                 c_811,c_39,c_17,c_18]) ).
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  ------                               Statistics
% 3.90/1.00  
% 3.90/1.00  ------ General
% 3.90/1.00  
% 3.90/1.00  abstr_ref_over_cycles:                  0
% 3.90/1.00  abstr_ref_under_cycles:                 0
% 3.90/1.00  gc_basic_clause_elim:                   0
% 3.90/1.00  forced_gc_time:                         0
% 3.90/1.00  parsing_time:                           0.014
% 3.90/1.00  unif_index_cands_time:                  0.
% 3.90/1.00  unif_index_add_time:                    0.
% 3.90/1.00  orderings_time:                         0.
% 3.90/1.00  out_proof_time:                         0.015
% 3.90/1.00  total_time:                             0.418
% 3.90/1.00  num_of_symbols:                         43
% 3.90/1.00  num_of_terms:                           8542
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing
% 3.90/1.00  
% 3.90/1.00  num_of_splits:                          0
% 3.90/1.00  num_of_split_atoms:                     0
% 3.90/1.00  num_of_reused_defs:                     0
% 3.90/1.00  num_eq_ax_congr_red:                    9
% 3.90/1.00  num_of_sem_filtered_clauses:            1
% 3.90/1.00  num_of_subtypes:                        0
% 3.90/1.00  monotx_restored_types:                  0
% 3.90/1.00  sat_num_of_epr_types:                   0
% 3.90/1.00  sat_num_of_non_cyclic_types:            0
% 3.90/1.00  sat_guarded_non_collapsed_types:        0
% 3.90/1.00  num_pure_diseq_elim:                    0
% 3.90/1.00  simp_replaced_by:                       0
% 3.90/1.00  res_preprocessed:                       93
% 3.90/1.00  prep_upred:                             0
% 3.90/1.00  prep_unflattend:                        0
% 3.90/1.00  smt_new_axioms:                         0
% 3.90/1.00  pred_elim_cands:                        4
% 3.90/1.00  pred_elim:                              0
% 3.90/1.00  pred_elim_cl:                           0
% 3.90/1.00  pred_elim_cycles:                       2
% 3.90/1.00  merged_defs:                            0
% 3.90/1.00  merged_defs_ncl:                        0
% 3.90/1.00  bin_hyper_res:                          0
% 3.90/1.00  prep_cycles:                            4
% 3.90/1.00  pred_elim_time:                         0.001
% 3.90/1.00  splitting_time:                         0.
% 3.90/1.00  sem_filter_time:                        0.
% 3.90/1.00  monotx_time:                            0.001
% 3.90/1.00  subtype_inf_time:                       0.
% 3.90/1.00  
% 3.90/1.00  ------ Problem properties
% 3.90/1.00  
% 3.90/1.00  clauses:                                18
% 3.90/1.00  conjectures:                            6
% 3.90/1.00  epr:                                    2
% 3.90/1.00  horn:                                   14
% 3.90/1.00  ground:                                 6
% 3.90/1.00  unary:                                  3
% 3.90/1.00  binary:                                 6
% 3.90/1.00  lits:                                   50
% 3.90/1.00  lits_eq:                                2
% 3.90/1.00  fd_pure:                                0
% 3.90/1.00  fd_pseudo:                              0
% 3.90/1.00  fd_cond:                                0
% 3.90/1.00  fd_pseudo_cond:                         0
% 3.90/1.00  ac_symbols:                             0
% 3.90/1.00  
% 3.90/1.00  ------ Propositional Solver
% 3.90/1.00  
% 3.90/1.00  prop_solver_calls:                      30
% 3.90/1.00  prop_fast_solver_calls:                 1120
% 3.90/1.00  smt_solver_calls:                       0
% 3.90/1.00  smt_fast_solver_calls:                  0
% 3.90/1.00  prop_num_of_clauses:                    4411
% 3.90/1.00  prop_preprocess_simplified:             6893
% 3.90/1.00  prop_fo_subsumed:                       85
% 3.90/1.00  prop_solver_time:                       0.
% 3.90/1.00  smt_solver_time:                        0.
% 3.90/1.00  smt_fast_solver_time:                   0.
% 3.90/1.00  prop_fast_solver_time:                  0.
% 3.90/1.00  prop_unsat_core_time:                   0.
% 3.90/1.00  
% 3.90/1.00  ------ QBF
% 3.90/1.00  
% 3.90/1.00  qbf_q_res:                              0
% 3.90/1.00  qbf_num_tautologies:                    0
% 3.90/1.00  qbf_prep_cycles:                        0
% 3.90/1.00  
% 3.90/1.00  ------ BMC1
% 3.90/1.00  
% 3.90/1.00  bmc1_current_bound:                     -1
% 3.90/1.00  bmc1_last_solved_bound:                 -1
% 3.90/1.00  bmc1_unsat_core_size:                   -1
% 3.90/1.00  bmc1_unsat_core_parents_size:           -1
% 3.90/1.00  bmc1_merge_next_fun:                    0
% 3.90/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.90/1.00  
% 3.90/1.00  ------ Instantiation
% 3.90/1.00  
% 3.90/1.00  inst_num_of_clauses:                    1037
% 3.90/1.00  inst_num_in_passive:                    525
% 3.90/1.00  inst_num_in_active:                     509
% 3.90/1.00  inst_num_in_unprocessed:                2
% 3.90/1.00  inst_num_of_loops:                      745
% 3.90/1.00  inst_num_of_learning_restarts:          0
% 3.90/1.00  inst_num_moves_active_passive:          230
% 3.90/1.00  inst_lit_activity:                      0
% 3.90/1.00  inst_lit_activity_moves:                0
% 3.90/1.00  inst_num_tautologies:                   0
% 3.90/1.00  inst_num_prop_implied:                  0
% 3.90/1.00  inst_num_existing_simplified:           0
% 3.90/1.00  inst_num_eq_res_simplified:             0
% 3.90/1.00  inst_num_child_elim:                    0
% 3.90/1.00  inst_num_of_dismatching_blockings:      827
% 3.90/1.00  inst_num_of_non_proper_insts:           1241
% 3.90/1.00  inst_num_of_duplicates:                 0
% 3.90/1.00  inst_inst_num_from_inst_to_res:         0
% 3.90/1.00  inst_dismatching_checking_time:         0.
% 3.90/1.00  
% 3.90/1.00  ------ Resolution
% 3.90/1.00  
% 3.90/1.00  res_num_of_clauses:                     0
% 3.90/1.00  res_num_in_passive:                     0
% 3.90/1.00  res_num_in_active:                      0
% 3.90/1.00  res_num_of_loops:                       97
% 3.90/1.00  res_forward_subset_subsumed:            50
% 3.90/1.00  res_backward_subset_subsumed:           0
% 3.90/1.00  res_forward_subsumed:                   0
% 3.90/1.00  res_backward_subsumed:                  0
% 3.90/1.00  res_forward_subsumption_resolution:     0
% 3.90/1.00  res_backward_subsumption_resolution:    0
% 3.90/1.00  res_clause_to_clause_subsumption:       1901
% 3.90/1.00  res_orphan_elimination:                 0
% 3.90/1.00  res_tautology_del:                      108
% 3.90/1.00  res_num_eq_res_simplified:              0
% 3.90/1.00  res_num_sel_changes:                    0
% 3.90/1.00  res_moves_from_active_to_pass:          0
% 3.90/1.00  
% 3.90/1.00  ------ Superposition
% 3.90/1.00  
% 3.90/1.00  sup_time_total:                         0.
% 3.90/1.00  sup_time_generating:                    0.
% 3.90/1.00  sup_time_sim_full:                      0.
% 3.90/1.00  sup_time_sim_immed:                     0.
% 3.90/1.00  
% 3.90/1.00  sup_num_of_clauses:                     437
% 3.90/1.00  sup_num_in_active:                      124
% 3.90/1.00  sup_num_in_passive:                     313
% 3.90/1.00  sup_num_of_loops:                       148
% 3.90/1.00  sup_fw_superposition:                   295
% 3.90/1.00  sup_bw_superposition:                   378
% 3.90/1.00  sup_immediate_simplified:               123
% 3.90/1.00  sup_given_eliminated:                   0
% 3.90/1.00  comparisons_done:                       0
% 3.90/1.00  comparisons_avoided:                    0
% 3.90/1.00  
% 3.90/1.00  ------ Simplifications
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  sim_fw_subset_subsumed:                 37
% 3.90/1.00  sim_bw_subset_subsumed:                 99
% 3.90/1.00  sim_fw_subsumed:                        33
% 3.90/1.00  sim_bw_subsumed:                        6
% 3.90/1.00  sim_fw_subsumption_res:                 2
% 3.90/1.00  sim_bw_subsumption_res:                 0
% 3.90/1.00  sim_tautology_del:                      19
% 3.90/1.00  sim_eq_tautology_del:                   10
% 3.90/1.00  sim_eq_res_simp:                        0
% 3.90/1.00  sim_fw_demodulated:                     0
% 3.90/1.00  sim_bw_demodulated:                     3
% 3.90/1.00  sim_light_normalised:                   57
% 3.90/1.00  sim_joinable_taut:                      0
% 3.90/1.00  sim_joinable_simp:                      0
% 3.90/1.00  sim_ac_normalised:                      0
% 3.90/1.00  sim_smt_subsumption:                    0
% 3.90/1.00  
%------------------------------------------------------------------------------
