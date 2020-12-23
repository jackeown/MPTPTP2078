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
% DateTime   : Thu Dec  3 12:18:09 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  187 (2741 expanded)
%              Number of clauses        :  132 (1068 expanded)
%              Number of leaves         :   18 ( 499 expanded)
%              Depth                    :   25
%              Number of atoms          :  618 (11993 expanded)
%              Number of equality atoms :  292 (1937 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

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

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f31])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_897,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_33625,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_280,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1356,plain,
    ( X0 != X1
    | X0 = k1_zfmisc_1(X2)
    | k1_zfmisc_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1932,plain,
    ( X0 != k1_zfmisc_1(X1)
    | X0 = k1_zfmisc_1(X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_4319,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_9695,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(X1)
    | k1_zfmisc_1(u1_struct_0(X2)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_4319])).

cnf(c_21385,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_zfmisc_1(X0)
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_9695])).

cnf(c_28978,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_21385])).

cnf(c_14,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_978,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_12039,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_25959,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_12039])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_675,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_687,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_692,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1290,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_692])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_693,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1519,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_693])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_691,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1201,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_691])).

cnf(c_2913,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1519,c_1201])).

cnf(c_2914,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2913])).

cnf(c_2921,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(superposition,[status(thm)],[c_675,c_2914])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_685,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3389,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2921,c_685])).

cnf(c_4530,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0)
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3389])).

cnf(c_22,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_43,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_45,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_6099,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4530,c_22,c_45])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_679,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6099,c_679])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_684,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6167,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6099,c_684])).

cnf(c_877,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_878,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_880,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_8906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6167,c_22,c_45,c_880])).

cnf(c_8907,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8906])).

cnf(c_8914,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_6107,c_8907])).

cnf(c_694,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_699,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_694,c_0])).

cnf(c_1624,plain,
    ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_684])).

cnf(c_3040,plain,
    ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_675,c_1624])).

cnf(c_15,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_681,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1594,plain,
    ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_681])).

cnf(c_5149,plain,
    ( v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | v2_compts_1(u1_struct_0(X0),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_1594])).

cnf(c_5,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_690,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2493,plain,
    ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_690])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_688,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3286,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_688])).

cnf(c_3320,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_5595,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | v2_compts_1(u1_struct_0(X0),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5149,c_22,c_3320])).

cnf(c_5596,plain,
    ( v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | v2_compts_1(u1_struct_0(X0),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5595])).

cnf(c_9089,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8914,c_5596])).

cnf(c_9210,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9089,c_8914])).

cnf(c_20,negated_conjecture,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6166,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6099,c_690])).

cnf(c_12411,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6166,c_22,c_45,c_880])).

cnf(c_12412,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12411])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_683,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12420,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12412,c_683])).

cnf(c_12419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12412,c_688])).

cnf(c_13498,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12420,c_22,c_45,c_880,c_12419])).

cnf(c_9090,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),X0) != iProver_top
    | v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8914,c_1594])).

cnf(c_9200,plain,
    ( v2_compts_1(sK1,X0) != iProver_top
    | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9090,c_8914])).

cnf(c_15139,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13498,c_9200])).

cnf(c_15136,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12412,c_9200])).

cnf(c_15177,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15136,c_6099])).

cnf(c_15214,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9210,c_22,c_23,c_45,c_880,c_6107,c_15139,c_15177])).

cnf(c_15216,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15214])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_925,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1351,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
    | X0 != k2_subset_1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_2165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | X0 != k2_subset_1(u1_struct_0(X1))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_13726,plain,
    ( ~ m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
    | sK1 != k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_281,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1175,plain,
    ( X0 != u1_struct_0(sK0)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1804,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_13454,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_682,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6326,plain,
    ( v2_compts_1(sK1,X0) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6107,c_682])).

cnf(c_7038,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | v2_compts_1(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6326,c_22])).

cnf(c_7039,plain,
    ( v2_compts_1(sK1,X0) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7038])).

cnf(c_9088,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8914,c_7039])).

cnf(c_18,negated_conjecture,
    ( v2_compts_1(sK1,sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_678,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2491,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_690])).

cnf(c_2598,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_22,c_45,c_880])).

cnf(c_2599,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2598])).

cnf(c_2604,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_688])).

cnf(c_2605,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_683])).

cnf(c_13428,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top
    | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9088,c_22,c_45,c_880,c_2604,c_2605])).

cnf(c_13429,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13428])).

cnf(c_13435,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13429,c_699])).

cnf(c_13436,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | v2_compts_1(sK1,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13435])).

cnf(c_935,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK0))
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1005,plain,
    ( m1_subset_1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_3542,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_13010,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3542])).

cnf(c_4925,plain,
    ( u1_struct_0(X0) != X1
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_7756,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != sK1
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_4925])).

cnf(c_6659,plain,
    ( k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1237,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_5311,plain,
    ( X0 != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | sK1 = X0
    | sK1 != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_6658,plain,
    ( k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | sK1 != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | sK1 = k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) ),
    inference(instantiation,[status(thm)],[c_5311])).

cnf(c_6159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6107])).

cnf(c_1908,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_3031,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != sK1
    | sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_1081,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_279,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1006,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_879,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_44,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_16,negated_conjecture,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33625,c_28978,c_25959,c_15216,c_13726,c_13454,c_13436,c_13010,c_8914,c_7756,c_6659,c_6658,c_6159,c_4530,c_3031,c_1081,c_1006,c_879,c_45,c_44,c_16,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 8.08/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/1.48  
% 8.08/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.08/1.48  
% 8.08/1.48  ------  iProver source info
% 8.08/1.48  
% 8.08/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.08/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.08/1.48  git: non_committed_changes: false
% 8.08/1.48  git: last_make_outside_of_git: false
% 8.08/1.48  
% 8.08/1.48  ------ 
% 8.08/1.48  
% 8.08/1.48  ------ Input Options
% 8.08/1.48  
% 8.08/1.48  --out_options                           all
% 8.08/1.48  --tptp_safe_out                         true
% 8.08/1.48  --problem_path                          ""
% 8.08/1.48  --include_path                          ""
% 8.08/1.48  --clausifier                            res/vclausify_rel
% 8.08/1.48  --clausifier_options                    --mode clausify
% 8.08/1.48  --stdin                                 false
% 8.08/1.48  --stats_out                             all
% 8.08/1.48  
% 8.08/1.48  ------ General Options
% 8.08/1.48  
% 8.08/1.48  --fof                                   false
% 8.08/1.48  --time_out_real                         305.
% 8.08/1.48  --time_out_virtual                      -1.
% 8.08/1.48  --symbol_type_check                     false
% 8.08/1.48  --clausify_out                          false
% 8.08/1.48  --sig_cnt_out                           false
% 8.08/1.48  --trig_cnt_out                          false
% 8.08/1.48  --trig_cnt_out_tolerance                1.
% 8.08/1.48  --trig_cnt_out_sk_spl                   false
% 8.08/1.48  --abstr_cl_out                          false
% 8.08/1.48  
% 8.08/1.48  ------ Global Options
% 8.08/1.48  
% 8.08/1.48  --schedule                              default
% 8.08/1.48  --add_important_lit                     false
% 8.08/1.48  --prop_solver_per_cl                    1000
% 8.08/1.48  --min_unsat_core                        false
% 8.08/1.48  --soft_assumptions                      false
% 8.08/1.48  --soft_lemma_size                       3
% 8.08/1.48  --prop_impl_unit_size                   0
% 8.08/1.48  --prop_impl_unit                        []
% 8.08/1.48  --share_sel_clauses                     true
% 8.08/1.48  --reset_solvers                         false
% 8.08/1.48  --bc_imp_inh                            [conj_cone]
% 8.08/1.48  --conj_cone_tolerance                   3.
% 8.08/1.48  --extra_neg_conj                        none
% 8.08/1.48  --large_theory_mode                     true
% 8.08/1.48  --prolific_symb_bound                   200
% 8.08/1.48  --lt_threshold                          2000
% 8.08/1.48  --clause_weak_htbl                      true
% 8.08/1.48  --gc_record_bc_elim                     false
% 8.08/1.48  
% 8.08/1.48  ------ Preprocessing Options
% 8.08/1.48  
% 8.08/1.48  --preprocessing_flag                    true
% 8.08/1.48  --time_out_prep_mult                    0.1
% 8.08/1.48  --splitting_mode                        input
% 8.08/1.48  --splitting_grd                         true
% 8.08/1.48  --splitting_cvd                         false
% 8.08/1.48  --splitting_cvd_svl                     false
% 8.08/1.48  --splitting_nvd                         32
% 8.08/1.48  --sub_typing                            true
% 8.08/1.48  --prep_gs_sim                           true
% 8.08/1.48  --prep_unflatten                        true
% 8.08/1.48  --prep_res_sim                          true
% 8.08/1.48  --prep_upred                            true
% 8.08/1.48  --prep_sem_filter                       exhaustive
% 8.08/1.48  --prep_sem_filter_out                   false
% 8.08/1.48  --pred_elim                             true
% 8.08/1.48  --res_sim_input                         true
% 8.08/1.48  --eq_ax_congr_red                       true
% 8.08/1.48  --pure_diseq_elim                       true
% 8.08/1.48  --brand_transform                       false
% 8.08/1.48  --non_eq_to_eq                          false
% 8.08/1.48  --prep_def_merge                        true
% 8.08/1.48  --prep_def_merge_prop_impl              false
% 8.08/1.48  --prep_def_merge_mbd                    true
% 8.08/1.48  --prep_def_merge_tr_red                 false
% 8.08/1.48  --prep_def_merge_tr_cl                  false
% 8.08/1.48  --smt_preprocessing                     true
% 8.08/1.48  --smt_ac_axioms                         fast
% 8.08/1.48  --preprocessed_out                      false
% 8.08/1.48  --preprocessed_stats                    false
% 8.08/1.48  
% 8.08/1.48  ------ Abstraction refinement Options
% 8.08/1.48  
% 8.08/1.48  --abstr_ref                             []
% 8.08/1.48  --abstr_ref_prep                        false
% 8.08/1.48  --abstr_ref_until_sat                   false
% 8.08/1.48  --abstr_ref_sig_restrict                funpre
% 8.08/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.48  --abstr_ref_under                       []
% 8.08/1.48  
% 8.08/1.48  ------ SAT Options
% 8.08/1.48  
% 8.08/1.48  --sat_mode                              false
% 8.08/1.48  --sat_fm_restart_options                ""
% 8.08/1.48  --sat_gr_def                            false
% 8.08/1.48  --sat_epr_types                         true
% 8.08/1.48  --sat_non_cyclic_types                  false
% 8.08/1.48  --sat_finite_models                     false
% 8.08/1.48  --sat_fm_lemmas                         false
% 8.08/1.48  --sat_fm_prep                           false
% 8.08/1.48  --sat_fm_uc_incr                        true
% 8.08/1.48  --sat_out_model                         small
% 8.08/1.48  --sat_out_clauses                       false
% 8.08/1.48  
% 8.08/1.48  ------ QBF Options
% 8.08/1.48  
% 8.08/1.48  --qbf_mode                              false
% 8.08/1.48  --qbf_elim_univ                         false
% 8.08/1.48  --qbf_dom_inst                          none
% 8.08/1.48  --qbf_dom_pre_inst                      false
% 8.08/1.48  --qbf_sk_in                             false
% 8.08/1.48  --qbf_pred_elim                         true
% 8.08/1.48  --qbf_split                             512
% 8.08/1.48  
% 8.08/1.48  ------ BMC1 Options
% 8.08/1.48  
% 8.08/1.48  --bmc1_incremental                      false
% 8.08/1.48  --bmc1_axioms                           reachable_all
% 8.08/1.48  --bmc1_min_bound                        0
% 8.08/1.48  --bmc1_max_bound                        -1
% 8.08/1.48  --bmc1_max_bound_default                -1
% 8.08/1.48  --bmc1_symbol_reachability              true
% 8.08/1.48  --bmc1_property_lemmas                  false
% 8.08/1.48  --bmc1_k_induction                      false
% 8.08/1.48  --bmc1_non_equiv_states                 false
% 8.08/1.48  --bmc1_deadlock                         false
% 8.08/1.48  --bmc1_ucm                              false
% 8.08/1.48  --bmc1_add_unsat_core                   none
% 8.08/1.48  --bmc1_unsat_core_children              false
% 8.08/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.48  --bmc1_out_stat                         full
% 8.08/1.48  --bmc1_ground_init                      false
% 8.08/1.48  --bmc1_pre_inst_next_state              false
% 8.08/1.48  --bmc1_pre_inst_state                   false
% 8.08/1.48  --bmc1_pre_inst_reach_state             false
% 8.08/1.48  --bmc1_out_unsat_core                   false
% 8.08/1.48  --bmc1_aig_witness_out                  false
% 8.08/1.48  --bmc1_verbose                          false
% 8.08/1.48  --bmc1_dump_clauses_tptp                false
% 8.08/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.48  --bmc1_dump_file                        -
% 8.08/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.48  --bmc1_ucm_extend_mode                  1
% 8.08/1.48  --bmc1_ucm_init_mode                    2
% 8.08/1.48  --bmc1_ucm_cone_mode                    none
% 8.08/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.48  --bmc1_ucm_relax_model                  4
% 8.08/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.48  --bmc1_ucm_layered_model                none
% 8.08/1.48  --bmc1_ucm_max_lemma_size               10
% 8.08/1.48  
% 8.08/1.48  ------ AIG Options
% 8.08/1.48  
% 8.08/1.48  --aig_mode                              false
% 8.08/1.48  
% 8.08/1.48  ------ Instantiation Options
% 8.08/1.48  
% 8.08/1.48  --instantiation_flag                    true
% 8.08/1.48  --inst_sos_flag                         false
% 8.08/1.48  --inst_sos_phase                        true
% 8.08/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.48  --inst_lit_sel_side                     num_symb
% 8.08/1.48  --inst_solver_per_active                1400
% 8.08/1.48  --inst_solver_calls_frac                1.
% 8.08/1.48  --inst_passive_queue_type               priority_queues
% 8.08/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.48  --inst_passive_queues_freq              [25;2]
% 8.08/1.48  --inst_dismatching                      true
% 8.08/1.48  --inst_eager_unprocessed_to_passive     true
% 8.08/1.48  --inst_prop_sim_given                   true
% 8.08/1.48  --inst_prop_sim_new                     false
% 8.08/1.48  --inst_subs_new                         false
% 8.08/1.48  --inst_eq_res_simp                      false
% 8.08/1.48  --inst_subs_given                       false
% 8.08/1.48  --inst_orphan_elimination               true
% 8.08/1.48  --inst_learning_loop_flag               true
% 8.08/1.48  --inst_learning_start                   3000
% 8.08/1.48  --inst_learning_factor                  2
% 8.08/1.48  --inst_start_prop_sim_after_learn       3
% 8.08/1.48  --inst_sel_renew                        solver
% 8.08/1.48  --inst_lit_activity_flag                true
% 8.08/1.48  --inst_restr_to_given                   false
% 8.08/1.48  --inst_activity_threshold               500
% 8.08/1.48  --inst_out_proof                        true
% 8.08/1.48  
% 8.08/1.48  ------ Resolution Options
% 8.08/1.48  
% 8.08/1.48  --resolution_flag                       true
% 8.08/1.48  --res_lit_sel                           adaptive
% 8.08/1.48  --res_lit_sel_side                      none
% 8.08/1.48  --res_ordering                          kbo
% 8.08/1.48  --res_to_prop_solver                    active
% 8.08/1.48  --res_prop_simpl_new                    false
% 8.08/1.48  --res_prop_simpl_given                  true
% 8.08/1.48  --res_passive_queue_type                priority_queues
% 8.08/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.48  --res_passive_queues_freq               [15;5]
% 8.08/1.48  --res_forward_subs                      full
% 8.08/1.48  --res_backward_subs                     full
% 8.08/1.48  --res_forward_subs_resolution           true
% 8.08/1.48  --res_backward_subs_resolution          true
% 8.08/1.48  --res_orphan_elimination                true
% 8.08/1.48  --res_time_limit                        2.
% 8.08/1.48  --res_out_proof                         true
% 8.08/1.48  
% 8.08/1.48  ------ Superposition Options
% 8.08/1.48  
% 8.08/1.48  --superposition_flag                    true
% 8.08/1.48  --sup_passive_queue_type                priority_queues
% 8.08/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.08/1.48  --demod_completeness_check              fast
% 8.08/1.48  --demod_use_ground                      true
% 8.08/1.48  --sup_to_prop_solver                    passive
% 8.08/1.48  --sup_prop_simpl_new                    true
% 8.08/1.48  --sup_prop_simpl_given                  true
% 8.08/1.48  --sup_fun_splitting                     false
% 8.08/1.48  --sup_smt_interval                      50000
% 8.08/1.48  
% 8.08/1.48  ------ Superposition Simplification Setup
% 8.08/1.48  
% 8.08/1.48  --sup_indices_passive                   []
% 8.08/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.48  --sup_full_bw                           [BwDemod]
% 8.08/1.48  --sup_immed_triv                        [TrivRules]
% 8.08/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.48  --sup_immed_bw_main                     []
% 8.08/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.48  
% 8.08/1.48  ------ Combination Options
% 8.08/1.48  
% 8.08/1.48  --comb_res_mult                         3
% 8.08/1.48  --comb_sup_mult                         2
% 8.08/1.48  --comb_inst_mult                        10
% 8.08/1.48  
% 8.08/1.48  ------ Debug Options
% 8.08/1.48  
% 8.08/1.48  --dbg_backtrace                         false
% 8.08/1.48  --dbg_dump_prop_clauses                 false
% 8.08/1.48  --dbg_dump_prop_clauses_file            -
% 8.08/1.48  --dbg_out_stat                          false
% 8.08/1.48  ------ Parsing...
% 8.08/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.08/1.48  
% 8.08/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.08/1.48  
% 8.08/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.08/1.48  
% 8.08/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.48  ------ Proving...
% 8.08/1.48  ------ Problem Properties 
% 8.08/1.48  
% 8.08/1.48  
% 8.08/1.48  clauses                                 22
% 8.08/1.48  conjectures                             6
% 8.08/1.48  EPR                                     2
% 8.08/1.48  Horn                                    18
% 8.08/1.48  unary                                   3
% 8.08/1.48  binary                                  7
% 8.08/1.48  lits                                    61
% 8.08/1.48  lits eq                                 7
% 8.08/1.48  fd_pure                                 0
% 8.08/1.48  fd_pseudo                               0
% 8.08/1.48  fd_cond                                 0
% 8.08/1.48  fd_pseudo_cond                          2
% 8.08/1.48  AC symbols                              0
% 8.08/1.48  
% 8.08/1.48  ------ Schedule dynamic 5 is on 
% 8.08/1.48  
% 8.08/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.08/1.48  
% 8.08/1.48  
% 8.08/1.48  ------ 
% 8.08/1.48  Current options:
% 8.08/1.48  ------ 
% 8.08/1.48  
% 8.08/1.48  ------ Input Options
% 8.08/1.48  
% 8.08/1.48  --out_options                           all
% 8.08/1.48  --tptp_safe_out                         true
% 8.08/1.48  --problem_path                          ""
% 8.08/1.48  --include_path                          ""
% 8.08/1.48  --clausifier                            res/vclausify_rel
% 8.08/1.48  --clausifier_options                    --mode clausify
% 8.08/1.48  --stdin                                 false
% 8.08/1.48  --stats_out                             all
% 8.08/1.48  
% 8.08/1.48  ------ General Options
% 8.08/1.48  
% 8.08/1.48  --fof                                   false
% 8.08/1.48  --time_out_real                         305.
% 8.08/1.48  --time_out_virtual                      -1.
% 8.08/1.48  --symbol_type_check                     false
% 8.08/1.48  --clausify_out                          false
% 8.08/1.48  --sig_cnt_out                           false
% 8.08/1.48  --trig_cnt_out                          false
% 8.08/1.48  --trig_cnt_out_tolerance                1.
% 8.08/1.48  --trig_cnt_out_sk_spl                   false
% 8.08/1.48  --abstr_cl_out                          false
% 8.08/1.48  
% 8.08/1.48  ------ Global Options
% 8.08/1.48  
% 8.08/1.48  --schedule                              default
% 8.08/1.48  --add_important_lit                     false
% 8.08/1.48  --prop_solver_per_cl                    1000
% 8.08/1.48  --min_unsat_core                        false
% 8.08/1.48  --soft_assumptions                      false
% 8.08/1.48  --soft_lemma_size                       3
% 8.08/1.48  --prop_impl_unit_size                   0
% 8.08/1.48  --prop_impl_unit                        []
% 8.08/1.48  --share_sel_clauses                     true
% 8.08/1.48  --reset_solvers                         false
% 8.08/1.48  --bc_imp_inh                            [conj_cone]
% 8.08/1.48  --conj_cone_tolerance                   3.
% 8.08/1.48  --extra_neg_conj                        none
% 8.08/1.48  --large_theory_mode                     true
% 8.08/1.48  --prolific_symb_bound                   200
% 8.08/1.48  --lt_threshold                          2000
% 8.08/1.48  --clause_weak_htbl                      true
% 8.08/1.48  --gc_record_bc_elim                     false
% 8.08/1.48  
% 8.08/1.48  ------ Preprocessing Options
% 8.08/1.48  
% 8.08/1.48  --preprocessing_flag                    true
% 8.08/1.48  --time_out_prep_mult                    0.1
% 8.08/1.48  --splitting_mode                        input
% 8.08/1.48  --splitting_grd                         true
% 8.08/1.48  --splitting_cvd                         false
% 8.08/1.48  --splitting_cvd_svl                     false
% 8.08/1.48  --splitting_nvd                         32
% 8.08/1.48  --sub_typing                            true
% 8.08/1.48  --prep_gs_sim                           true
% 8.08/1.48  --prep_unflatten                        true
% 8.08/1.48  --prep_res_sim                          true
% 8.08/1.48  --prep_upred                            true
% 8.08/1.48  --prep_sem_filter                       exhaustive
% 8.08/1.48  --prep_sem_filter_out                   false
% 8.08/1.48  --pred_elim                             true
% 8.08/1.48  --res_sim_input                         true
% 8.08/1.48  --eq_ax_congr_red                       true
% 8.08/1.48  --pure_diseq_elim                       true
% 8.08/1.48  --brand_transform                       false
% 8.08/1.48  --non_eq_to_eq                          false
% 8.08/1.48  --prep_def_merge                        true
% 8.08/1.48  --prep_def_merge_prop_impl              false
% 8.08/1.48  --prep_def_merge_mbd                    true
% 8.08/1.48  --prep_def_merge_tr_red                 false
% 8.08/1.48  --prep_def_merge_tr_cl                  false
% 8.08/1.48  --smt_preprocessing                     true
% 8.08/1.48  --smt_ac_axioms                         fast
% 8.08/1.48  --preprocessed_out                      false
% 8.08/1.48  --preprocessed_stats                    false
% 8.08/1.48  
% 8.08/1.48  ------ Abstraction refinement Options
% 8.08/1.48  
% 8.08/1.48  --abstr_ref                             []
% 8.08/1.48  --abstr_ref_prep                        false
% 8.08/1.48  --abstr_ref_until_sat                   false
% 8.08/1.48  --abstr_ref_sig_restrict                funpre
% 8.08/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.48  --abstr_ref_under                       []
% 8.08/1.48  
% 8.08/1.48  ------ SAT Options
% 8.08/1.48  
% 8.08/1.48  --sat_mode                              false
% 8.08/1.48  --sat_fm_restart_options                ""
% 8.08/1.48  --sat_gr_def                            false
% 8.08/1.48  --sat_epr_types                         true
% 8.08/1.48  --sat_non_cyclic_types                  false
% 8.08/1.48  --sat_finite_models                     false
% 8.08/1.48  --sat_fm_lemmas                         false
% 8.08/1.48  --sat_fm_prep                           false
% 8.08/1.48  --sat_fm_uc_incr                        true
% 8.08/1.48  --sat_out_model                         small
% 8.08/1.48  --sat_out_clauses                       false
% 8.08/1.48  
% 8.08/1.48  ------ QBF Options
% 8.08/1.48  
% 8.08/1.48  --qbf_mode                              false
% 8.08/1.48  --qbf_elim_univ                         false
% 8.08/1.48  --qbf_dom_inst                          none
% 8.08/1.48  --qbf_dom_pre_inst                      false
% 8.08/1.48  --qbf_sk_in                             false
% 8.08/1.48  --qbf_pred_elim                         true
% 8.08/1.48  --qbf_split                             512
% 8.08/1.48  
% 8.08/1.48  ------ BMC1 Options
% 8.08/1.48  
% 8.08/1.48  --bmc1_incremental                      false
% 8.08/1.48  --bmc1_axioms                           reachable_all
% 8.08/1.48  --bmc1_min_bound                        0
% 8.08/1.48  --bmc1_max_bound                        -1
% 8.08/1.48  --bmc1_max_bound_default                -1
% 8.08/1.48  --bmc1_symbol_reachability              true
% 8.08/1.48  --bmc1_property_lemmas                  false
% 8.08/1.48  --bmc1_k_induction                      false
% 8.08/1.48  --bmc1_non_equiv_states                 false
% 8.08/1.48  --bmc1_deadlock                         false
% 8.08/1.48  --bmc1_ucm                              false
% 8.08/1.48  --bmc1_add_unsat_core                   none
% 8.08/1.48  --bmc1_unsat_core_children              false
% 8.08/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.48  --bmc1_out_stat                         full
% 8.08/1.48  --bmc1_ground_init                      false
% 8.08/1.48  --bmc1_pre_inst_next_state              false
% 8.08/1.48  --bmc1_pre_inst_state                   false
% 8.08/1.48  --bmc1_pre_inst_reach_state             false
% 8.08/1.48  --bmc1_out_unsat_core                   false
% 8.08/1.48  --bmc1_aig_witness_out                  false
% 8.08/1.48  --bmc1_verbose                          false
% 8.08/1.48  --bmc1_dump_clauses_tptp                false
% 8.08/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.48  --bmc1_dump_file                        -
% 8.08/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.48  --bmc1_ucm_extend_mode                  1
% 8.08/1.48  --bmc1_ucm_init_mode                    2
% 8.08/1.48  --bmc1_ucm_cone_mode                    none
% 8.08/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.48  --bmc1_ucm_relax_model                  4
% 8.08/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.48  --bmc1_ucm_layered_model                none
% 8.08/1.48  --bmc1_ucm_max_lemma_size               10
% 8.08/1.48  
% 8.08/1.48  ------ AIG Options
% 8.08/1.48  
% 8.08/1.48  --aig_mode                              false
% 8.08/1.48  
% 8.08/1.48  ------ Instantiation Options
% 8.08/1.48  
% 8.08/1.48  --instantiation_flag                    true
% 8.08/1.48  --inst_sos_flag                         false
% 8.08/1.48  --inst_sos_phase                        true
% 8.08/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.48  --inst_lit_sel_side                     none
% 8.08/1.48  --inst_solver_per_active                1400
% 8.08/1.48  --inst_solver_calls_frac                1.
% 8.08/1.48  --inst_passive_queue_type               priority_queues
% 8.08/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.48  --inst_passive_queues_freq              [25;2]
% 8.08/1.48  --inst_dismatching                      true
% 8.08/1.48  --inst_eager_unprocessed_to_passive     true
% 8.08/1.48  --inst_prop_sim_given                   true
% 8.08/1.48  --inst_prop_sim_new                     false
% 8.08/1.48  --inst_subs_new                         false
% 8.08/1.48  --inst_eq_res_simp                      false
% 8.08/1.48  --inst_subs_given                       false
% 8.08/1.48  --inst_orphan_elimination               true
% 8.08/1.48  --inst_learning_loop_flag               true
% 8.08/1.48  --inst_learning_start                   3000
% 8.08/1.48  --inst_learning_factor                  2
% 8.08/1.48  --inst_start_prop_sim_after_learn       3
% 8.08/1.48  --inst_sel_renew                        solver
% 8.08/1.48  --inst_lit_activity_flag                true
% 8.08/1.48  --inst_restr_to_given                   false
% 8.08/1.48  --inst_activity_threshold               500
% 8.08/1.48  --inst_out_proof                        true
% 8.08/1.48  
% 8.08/1.48  ------ Resolution Options
% 8.08/1.48  
% 8.08/1.48  --resolution_flag                       false
% 8.08/1.48  --res_lit_sel                           adaptive
% 8.08/1.48  --res_lit_sel_side                      none
% 8.08/1.48  --res_ordering                          kbo
% 8.08/1.48  --res_to_prop_solver                    active
% 8.08/1.48  --res_prop_simpl_new                    false
% 8.08/1.48  --res_prop_simpl_given                  true
% 8.08/1.48  --res_passive_queue_type                priority_queues
% 8.08/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.48  --res_passive_queues_freq               [15;5]
% 8.08/1.48  --res_forward_subs                      full
% 8.08/1.48  --res_backward_subs                     full
% 8.08/1.48  --res_forward_subs_resolution           true
% 8.08/1.48  --res_backward_subs_resolution          true
% 8.08/1.48  --res_orphan_elimination                true
% 8.08/1.48  --res_time_limit                        2.
% 8.08/1.48  --res_out_proof                         true
% 8.08/1.48  
% 8.08/1.48  ------ Superposition Options
% 8.08/1.48  
% 8.08/1.48  --superposition_flag                    true
% 8.08/1.48  --sup_passive_queue_type                priority_queues
% 8.08/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.08/1.48  --demod_completeness_check              fast
% 8.08/1.48  --demod_use_ground                      true
% 8.08/1.48  --sup_to_prop_solver                    passive
% 8.08/1.48  --sup_prop_simpl_new                    true
% 8.08/1.48  --sup_prop_simpl_given                  true
% 8.08/1.48  --sup_fun_splitting                     false
% 8.08/1.48  --sup_smt_interval                      50000
% 8.08/1.48  
% 8.08/1.48  ------ Superposition Simplification Setup
% 8.08/1.48  
% 8.08/1.48  --sup_indices_passive                   []
% 8.08/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.48  --sup_full_bw                           [BwDemod]
% 8.08/1.48  --sup_immed_triv                        [TrivRules]
% 8.08/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.48  --sup_immed_bw_main                     []
% 8.08/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.48  
% 8.08/1.48  ------ Combination Options
% 8.08/1.48  
% 8.08/1.48  --comb_res_mult                         3
% 8.08/1.48  --comb_sup_mult                         2
% 8.08/1.48  --comb_inst_mult                        10
% 8.08/1.48  
% 8.08/1.48  ------ Debug Options
% 8.08/1.48  
% 8.08/1.48  --dbg_backtrace                         false
% 8.08/1.48  --dbg_dump_prop_clauses                 false
% 8.08/1.48  --dbg_dump_prop_clauses_file            -
% 8.08/1.48  --dbg_out_stat                          false
% 8.08/1.48  
% 8.08/1.48  
% 8.08/1.48  
% 8.08/1.48  
% 8.08/1.48  ------ Proving...
% 8.08/1.48  
% 8.08/1.48  
% 8.08/1.48  % SZS status Theorem for theBenchmark.p
% 8.08/1.48  
% 8.08/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.08/1.48  
% 8.08/1.48  fof(f2,axiom,(
% 8.08/1.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f37,plain,(
% 8.08/1.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 8.08/1.48    inference(cnf_transformation,[],[f2])).
% 8.08/1.48  
% 8.08/1.48  fof(f11,axiom,(
% 8.08/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f26,plain,(
% 8.08/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(ennf_transformation,[],[f11])).
% 8.08/1.48  
% 8.08/1.48  fof(f27,plain,(
% 8.08/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(flattening,[],[f26])).
% 8.08/1.48  
% 8.08/1.48  fof(f30,plain,(
% 8.08/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(nnf_transformation,[],[f27])).
% 8.08/1.48  
% 8.08/1.48  fof(f51,plain,(
% 8.08/1.48    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f30])).
% 8.08/1.48  
% 8.08/1.48  fof(f58,plain,(
% 8.08/1.48    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(equality_resolution,[],[f51])).
% 8.08/1.48  
% 8.08/1.48  fof(f12,conjecture,(
% 8.08/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f13,negated_conjecture,(
% 8.08/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 8.08/1.48    inference(negated_conjecture,[],[f12])).
% 8.08/1.48  
% 8.08/1.48  fof(f14,plain,(
% 8.08/1.48    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 8.08/1.48    inference(pure_predicate_removal,[],[f13])).
% 8.08/1.48  
% 8.08/1.48  fof(f15,plain,(
% 8.08/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 8.08/1.48    inference(pure_predicate_removal,[],[f14])).
% 8.08/1.48  
% 8.08/1.48  fof(f28,plain,(
% 8.08/1.48    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 8.08/1.48    inference(ennf_transformation,[],[f15])).
% 8.08/1.48  
% 8.08/1.48  fof(f31,plain,(
% 8.08/1.48    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 8.08/1.48    inference(nnf_transformation,[],[f28])).
% 8.08/1.48  
% 8.08/1.48  fof(f32,plain,(
% 8.08/1.48    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 8.08/1.48    inference(flattening,[],[f31])).
% 8.08/1.48  
% 8.08/1.48  fof(f34,plain,(
% 8.08/1.48    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(sK1,X0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(sK1,X0))))) )),
% 8.08/1.48    introduced(choice_axiom,[])).
% 8.08/1.48  
% 8.08/1.48  fof(f33,plain,(
% 8.08/1.48    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0))),
% 8.08/1.48    introduced(choice_axiom,[])).
% 8.08/1.48  
% 8.08/1.48  fof(f35,plain,(
% 8.08/1.48    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0)),
% 8.08/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 8.08/1.48  
% 8.08/1.48  fof(f52,plain,(
% 8.08/1.48    l1_pre_topc(sK0)),
% 8.08/1.48    inference(cnf_transformation,[],[f35])).
% 8.08/1.48  
% 8.08/1.48  fof(f7,axiom,(
% 8.08/1.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f22,plain,(
% 8.08/1.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(ennf_transformation,[],[f7])).
% 8.08/1.48  
% 8.08/1.48  fof(f44,plain,(
% 8.08/1.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f22])).
% 8.08/1.48  
% 8.08/1.48  fof(f4,axiom,(
% 8.08/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f18,plain,(
% 8.08/1.48    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.08/1.48    inference(ennf_transformation,[],[f4])).
% 8.08/1.48  
% 8.08/1.48  fof(f40,plain,(
% 8.08/1.48    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.08/1.48    inference(cnf_transformation,[],[f18])).
% 8.08/1.48  
% 8.08/1.48  fof(f3,axiom,(
% 8.08/1.48    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f16,plain,(
% 8.08/1.48    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(ennf_transformation,[],[f3])).
% 8.08/1.48  
% 8.08/1.48  fof(f17,plain,(
% 8.08/1.48    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(flattening,[],[f16])).
% 8.08/1.48  
% 8.08/1.48  fof(f38,plain,(
% 8.08/1.48    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f17])).
% 8.08/1.48  
% 8.08/1.48  fof(f39,plain,(
% 8.08/1.48    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.08/1.48    inference(cnf_transformation,[],[f18])).
% 8.08/1.48  
% 8.08/1.48  fof(f8,axiom,(
% 8.08/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f23,plain,(
% 8.08/1.48    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.08/1.48    inference(ennf_transformation,[],[f8])).
% 8.08/1.48  
% 8.08/1.48  fof(f45,plain,(
% 8.08/1.48    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 8.08/1.48    inference(cnf_transformation,[],[f23])).
% 8.08/1.48  
% 8.08/1.48  fof(f56,plain,(
% 8.08/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.08/1.48    inference(cnf_transformation,[],[f35])).
% 8.08/1.48  
% 8.08/1.48  fof(f9,axiom,(
% 8.08/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f24,plain,(
% 8.08/1.48    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(ennf_transformation,[],[f9])).
% 8.08/1.48  
% 8.08/1.48  fof(f47,plain,(
% 8.08/1.48    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f24])).
% 8.08/1.48  
% 8.08/1.48  fof(f1,axiom,(
% 8.08/1.48    ! [X0] : k2_subset_1(X0) = X0),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f36,plain,(
% 8.08/1.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 8.08/1.48    inference(cnf_transformation,[],[f1])).
% 8.08/1.48  
% 8.08/1.48  fof(f50,plain,(
% 8.08/1.48    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f30])).
% 8.08/1.48  
% 8.08/1.48  fof(f59,plain,(
% 8.08/1.48    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(equality_resolution,[],[f50])).
% 8.08/1.48  
% 8.08/1.48  fof(f5,axiom,(
% 8.08/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f19,plain,(
% 8.08/1.48    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.08/1.48    inference(ennf_transformation,[],[f5])).
% 8.08/1.48  
% 8.08/1.48  fof(f20,plain,(
% 8.08/1.48    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(flattening,[],[f19])).
% 8.08/1.48  
% 8.08/1.48  fof(f42,plain,(
% 8.08/1.48    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f20])).
% 8.08/1.48  
% 8.08/1.48  fof(f6,axiom,(
% 8.08/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f21,plain,(
% 8.08/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(ennf_transformation,[],[f6])).
% 8.08/1.48  
% 8.08/1.48  fof(f43,plain,(
% 8.08/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f21])).
% 8.08/1.48  
% 8.08/1.48  fof(f53,plain,(
% 8.08/1.48    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 8.08/1.48    inference(cnf_transformation,[],[f35])).
% 8.08/1.48  
% 8.08/1.48  fof(f10,axiom,(
% 8.08/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 8.08/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.48  
% 8.08/1.48  fof(f25,plain,(
% 8.08/1.48    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(ennf_transformation,[],[f10])).
% 8.08/1.48  
% 8.08/1.48  fof(f29,plain,(
% 8.08/1.48    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 8.08/1.48    inference(nnf_transformation,[],[f25])).
% 8.08/1.48  
% 8.08/1.48  fof(f49,plain,(
% 8.08/1.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 8.08/1.48    inference(cnf_transformation,[],[f29])).
% 8.08/1.48  
% 8.08/1.48  fof(f55,plain,(
% 8.08/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(sK1,sK0)),
% 8.08/1.48    inference(cnf_transformation,[],[f35])).
% 8.08/1.48  
% 8.08/1.48  fof(f57,plain,(
% 8.08/1.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 8.08/1.48    inference(cnf_transformation,[],[f35])).
% 8.08/1.48  
% 8.08/1.48  cnf(c_1,plain,
% 8.08/1.48      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 8.08/1.48      inference(cnf_transformation,[],[f37]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_897,plain,
% 8.08/1.48      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_33625,plain,
% 8.08/1.48      ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_897]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_280,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_1356,plain,
% 8.08/1.48      ( X0 != X1 | X0 = k1_zfmisc_1(X2) | k1_zfmisc_1(X2) != X1 ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_280]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_1932,plain,
% 8.08/1.48      ( X0 != k1_zfmisc_1(X1)
% 8.08/1.48      | X0 = k1_zfmisc_1(X2)
% 8.08/1.48      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_1356]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_4319,plain,
% 8.08/1.48      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 8.08/1.48      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
% 8.08/1.48      | k1_zfmisc_1(X0) = k1_zfmisc_1(X2) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_1932]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_9695,plain,
% 8.08/1.48      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 8.08/1.48      | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(X1)
% 8.08/1.48      | k1_zfmisc_1(u1_struct_0(X2)) = k1_zfmisc_1(X0) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_4319]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_21385,plain,
% 8.08/1.48      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 8.08/1.48      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_zfmisc_1(X0)
% 8.08/1.48      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != k1_zfmisc_1(sK1) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_9695]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_28978,plain,
% 8.08/1.48      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
% 8.08/1.48      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != k1_zfmisc_1(sK1) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_21385]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_14,plain,
% 8.08/1.48      ( ~ v2_compts_1(X0,X1)
% 8.08/1.48      | v2_compts_1(X0,X2)
% 8.08/1.48      | ~ m1_pre_topc(X1,X2)
% 8.08/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.08/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 8.08/1.48      | ~ l1_pre_topc(X2) ),
% 8.08/1.48      inference(cnf_transformation,[],[f58]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_978,plain,
% 8.08/1.48      ( ~ v2_compts_1(sK1,X0)
% 8.08/1.48      | v2_compts_1(sK1,X1)
% 8.08/1.48      | ~ m1_pre_topc(X0,X1)
% 8.08/1.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
% 8.08/1.48      | ~ l1_pre_topc(X1) ),
% 8.08/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 8.08/1.48  
% 8.08/1.48  cnf(c_12039,plain,
% 8.08/1.48      ( ~ v2_compts_1(sK1,X0)
% 8.08/1.48      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 8.08/1.48      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 8.08/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_978]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_25959,plain,
% 8.08/1.49      ( ~ v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 8.08/1.49      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 8.08/1.49      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 8.08/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_12039]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_21,negated_conjecture,
% 8.08/1.49      ( l1_pre_topc(sK0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_675,plain,
% 8.08/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_8,plain,
% 8.08/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.08/1.49      | ~ l1_pre_topc(X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_687,plain,
% 8.08/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3,plain,
% 8.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f40]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_692,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1290,plain,
% 8.08/1.49      ( l1_pre_topc(X0) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_687,c_692]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2,plain,
% 8.08/1.49      ( ~ l1_pre_topc(X0)
% 8.08/1.49      | ~ v1_pre_topc(X0)
% 8.08/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 8.08/1.49      inference(cnf_transformation,[],[f38]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_693,plain,
% 8.08/1.49      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top
% 8.08/1.49      | v1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1519,plain,
% 8.08/1.49      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top
% 8.08/1.49      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_1290,c_693]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_4,plain,
% 8.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 8.08/1.49      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f39]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_691,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 8.08/1.49      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1201,plain,
% 8.08/1.49      ( l1_pre_topc(X0) != iProver_top
% 8.08/1.49      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_687,c_691]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2913,plain,
% 8.08/1.49      ( l1_pre_topc(X0) != iProver_top
% 8.08/1.49      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_1519,c_1201]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2914,plain,
% 8.08/1.49      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_2913]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2921,plain,
% 8.08/1.49      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_675,c_2914]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_10,plain,
% 8.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 8.08/1.49      | X2 = X1
% 8.08/1.49      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f45]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_685,plain,
% 8.08/1.49      ( X0 = X1
% 8.08/1.49      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 8.08/1.49      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3389,plain,
% 8.08/1.49      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 8.08/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 8.08/1.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_2921,c_685]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_4530,plain,
% 8.08/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0)
% 8.08/1.49      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.08/1.49      inference(equality_resolution,[status(thm)],[c_3389]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_22,plain,
% 8.08/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_43,plain,
% 8.08/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_45,plain,
% 8.08/1.49      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 8.08/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_43]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6099,plain,
% 8.08/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_4530,c_22,c_45]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_17,negated_conjecture,
% 8.08/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.08/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_679,plain,
% 8.08/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6107,plain,
% 8.08/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.08/1.49      inference(demodulation,[status(thm)],[c_6099,c_679]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_11,plain,
% 8.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.08/1.49      | ~ l1_pre_topc(X1)
% 8.08/1.49      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 8.08/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_684,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 8.08/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6167,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_6099,c_684]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_877,plain,
% 8.08/1.49      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_878,plain,
% 8.08/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_880,plain,
% 8.08/1.49      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_878]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_8906,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0 ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_6167,c_22,c_45,c_880]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_8907,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_8906]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_8914,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_6107,c_8907]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_694,plain,
% 8.08/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_0,plain,
% 8.08/1.49      ( k2_subset_1(X0) = X0 ),
% 8.08/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_699,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.08/1.49      inference(light_normalisation,[status(thm)],[c_694,c_0]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1624,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_699,c_684]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3040,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_675,c_1624]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15,plain,
% 8.08/1.49      ( ~ v2_compts_1(X0,X1)
% 8.08/1.49      | v2_compts_1(X0,X2)
% 8.08/1.49      | ~ m1_pre_topc(X2,X1)
% 8.08/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 8.08/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.08/1.49      | ~ l1_pre_topc(X1) ),
% 8.08/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_681,plain,
% 8.08/1.49      ( v2_compts_1(X0,X1) != iProver_top
% 8.08/1.49      | v2_compts_1(X0,X2) = iProver_top
% 8.08/1.49      | m1_pre_topc(X2,X1) != iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1594,plain,
% 8.08/1.49      ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
% 8.08/1.49      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 8.08/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 8.08/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_699,c_681]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5149,plain,
% 8.08/1.49      ( v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 8.08/1.49      | v2_compts_1(u1_struct_0(X0),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_pre_topc(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_3040,c_1594]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 8.08/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.49      | ~ l1_pre_topc(X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_690,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 8.08/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2493,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_699,c_690]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_7,plain,
% 8.08/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_688,plain,
% 8.08/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.08/1.49      | l1_pre_topc(X1) != iProver_top
% 8.08/1.49      | l1_pre_topc(X0) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3286,plain,
% 8.08/1.49      ( l1_pre_topc(X0) != iProver_top
% 8.08/1.49      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_2493,c_688]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3320,plain,
% 8.08/1.49      ( l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 8.08/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_3286]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5595,plain,
% 8.08/1.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_pre_topc(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | v2_compts_1(u1_struct_0(X0),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_5149,c_22,c_3320]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5596,plain,
% 8.08/1.49      ( v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 8.08/1.49      | v2_compts_1(u1_struct_0(X0),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_pre_topc(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_5595]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_9089,plain,
% 8.08/1.49      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_8914,c_5596]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_9210,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.08/1.49      inference(light_normalisation,[status(thm)],[c_9089,c_8914]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_20,negated_conjecture,
% 8.08/1.49      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 8.08/1.49      | v2_compts_1(sK1,sK0) ),
% 8.08/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_23,plain,
% 8.08/1.49      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6166,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_6099,c_690]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_12411,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_6166,c_22,c_45,c_880]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_12412,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_12411]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_12,plain,
% 8.08/1.49      ( m1_pre_topc(X0,X1)
% 8.08/1.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 8.08/1.49      | ~ l1_pre_topc(X0)
% 8.08/1.49      | ~ l1_pre_topc(X1) ),
% 8.08/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_683,plain,
% 8.08/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 8.08/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X1) != iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_12420,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0) = iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) != iProver_top
% 8.08/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_12412,c_683]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_12419,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_12412,c_688]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13498,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0) = iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_12420,c_22,c_45,c_880,c_12419]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_9090,plain,
% 8.08/1.49      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),X0) != iProver_top
% 8.08/1.49      | v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_8914,c_1594]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_9200,plain,
% 8.08/1.49      ( v2_compts_1(sK1,X0) != iProver_top
% 8.08/1.49      | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.08/1.49      inference(light_normalisation,[status(thm)],[c_9090,c_8914]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15139,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_13498,c_9200]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15136,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_12412,c_9200]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15177,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 8.08/1.49      inference(light_normalisation,[status(thm)],[c_15136,c_6099]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15214,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_9210,c_22,c_23,c_45,c_880,c_6107,c_15139,c_15177]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15216,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
% 8.08/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_15214]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_282,plain,
% 8.08/1.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.08/1.49      theory(equality) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_925,plain,
% 8.08/1.49      ( m1_subset_1(X0,X1)
% 8.08/1.49      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 8.08/1.49      | X1 != k1_zfmisc_1(X2)
% 8.08/1.49      | X0 != k2_subset_1(X2) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_282]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1351,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.49      | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
% 8.08/1.49      | X0 != k2_subset_1(X1)
% 8.08/1.49      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_925]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2165,plain,
% 8.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.08/1.49      | ~ m1_subset_1(k2_subset_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
% 8.08/1.49      | X0 != k2_subset_1(u1_struct_0(X1))
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1351]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13726,plain,
% 8.08/1.49      ( ~ m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
% 8.08/1.49      | sK1 != k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_2165]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_281,plain,
% 8.08/1.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 8.08/1.49      theory(equality) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1175,plain,
% 8.08/1.49      ( X0 != u1_struct_0(sK0)
% 8.08/1.49      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_281]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1804,plain,
% 8.08/1.49      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1175]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13454,plain,
% 8.08/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(sK0)
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1804]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_682,plain,
% 8.08/1.49      ( v2_compts_1(X0,X1) != iProver_top
% 8.08/1.49      | v2_compts_1(X0,X2) = iProver_top
% 8.08/1.49      | m1_pre_topc(X1,X2) != iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 8.08/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.08/1.49      | l1_pre_topc(X2) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6326,plain,
% 8.08/1.49      ( v2_compts_1(sK1,X0) != iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.08/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_6107,c_682]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_7038,plain,
% 8.08/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.08/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,X0) != iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_6326,c_22]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_7039,plain,
% 8.08/1.49      ( v2_compts_1(sK1,X0) != iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_7038]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_9088,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_8914,c_7039]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_18,negated_conjecture,
% 8.08/1.49      ( v2_compts_1(sK1,sK0)
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
% 8.08/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_678,plain,
% 8.08/1.49      ( v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2491,plain,
% 8.08/1.49      ( v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_678,c_690]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2598,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_2491,c_22,c_45,c_880]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2599,plain,
% 8.08/1.49      ( v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_2598]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2604,plain,
% 8.08/1.49      ( v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_2599,c_688]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_2605,plain,
% 8.08/1.49      ( v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
% 8.08/1.49      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
% 8.08/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_2599,c_683]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13428,plain,
% 8.08/1.49      ( v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.08/1.49      inference(global_propositional_subsumption,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_9088,c_22,c_45,c_880,c_2604,c_2605]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13429,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top
% 8.08/1.49      | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
% 8.08/1.49      inference(renaming,[status(thm)],[c_13428]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13435,plain,
% 8.08/1.49      ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
% 8.08/1.49      | v2_compts_1(sK1,sK0) = iProver_top ),
% 8.08/1.49      inference(forward_subsumption_resolution,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_13429,c_699]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13436,plain,
% 8.08/1.49      ( ~ v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 8.08/1.49      | v2_compts_1(sK1,sK0) ),
% 8.08/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_13435]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_935,plain,
% 8.08/1.49      ( m1_subset_1(X0,X1)
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.08/1.49      | X1 != k1_zfmisc_1(u1_struct_0(sK0))
% 8.08/1.49      | X0 != sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_282]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1005,plain,
% 8.08/1.49      ( m1_subset_1(sK1,X0)
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.08/1.49      | X0 != k1_zfmisc_1(u1_struct_0(sK0))
% 8.08/1.49      | sK1 != sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_935]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3542,plain,
% 8.08/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 8.08/1.49      | sK1 != sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1005]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13010,plain,
% 8.08/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != k1_zfmisc_1(u1_struct_0(sK0))
% 8.08/1.49      | sK1 != sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_3542]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_4925,plain,
% 8.08/1.49      ( u1_struct_0(X0) != X1
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(X1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_281]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_7756,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != sK1
% 8.08/1.49      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_zfmisc_1(sK1) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_4925]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6659,plain,
% 8.08/1.49      ( k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1237,plain,
% 8.08/1.49      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_280]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_5311,plain,
% 8.08/1.49      ( X0 != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 8.08/1.49      | sK1 = X0
% 8.08/1.49      | sK1 != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1237]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6658,plain,
% 8.08/1.49      ( k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 8.08/1.49      | sK1 != u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 8.08/1.49      | sK1 = k2_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_5311]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_6159,plain,
% 8.08/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.08/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_6107]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1908,plain,
% 8.08/1.49      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1237]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_3031,plain,
% 8.08/1.49      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != sK1
% 8.08/1.49      | sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 8.08/1.49      | sK1 != sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_1908]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1081,plain,
% 8.08/1.49      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 8.08/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_279,plain,( X0 = X0 ),theory(equality) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_1006,plain,
% 8.08/1.49      ( sK1 = sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_279]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_879,plain,
% 8.08/1.49      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.08/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_877]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_44,plain,
% 8.08/1.49      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.08/1.49      | ~ l1_pre_topc(sK0) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_16,negated_conjecture,
% 8.08/1.49      ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 8.08/1.49      | ~ v2_compts_1(sK1,sK0)
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 8.08/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.08/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(contradiction,plain,
% 8.08/1.49      ( $false ),
% 8.08/1.49      inference(minisat,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_33625,c_28978,c_25959,c_15216,c_13726,c_13454,c_13436,
% 8.08/1.49                 c_13010,c_8914,c_7756,c_6659,c_6658,c_6159,c_4530,
% 8.08/1.49                 c_3031,c_1081,c_1006,c_879,c_45,c_44,c_16,c_22,c_21]) ).
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  ------                               Statistics
% 8.08/1.49  
% 8.08/1.49  ------ General
% 8.08/1.49  
% 8.08/1.49  abstr_ref_over_cycles:                  0
% 8.08/1.49  abstr_ref_under_cycles:                 0
% 8.08/1.49  gc_basic_clause_elim:                   0
% 8.08/1.49  forced_gc_time:                         0
% 8.08/1.49  parsing_time:                           0.009
% 8.08/1.49  unif_index_cands_time:                  0.
% 8.08/1.49  unif_index_add_time:                    0.
% 8.08/1.49  orderings_time:                         0.
% 8.08/1.49  out_proof_time:                         0.018
% 8.08/1.49  total_time:                             0.951
% 8.08/1.49  num_of_symbols:                         44
% 8.08/1.49  num_of_terms:                           28218
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing
% 8.08/1.49  
% 8.08/1.49  num_of_splits:                          0
% 8.08/1.49  num_of_split_atoms:                     0
% 8.08/1.49  num_of_reused_defs:                     0
% 8.08/1.49  num_eq_ax_congr_red:                    6
% 8.08/1.49  num_of_sem_filtered_clauses:            1
% 8.08/1.49  num_of_subtypes:                        0
% 8.08/1.49  monotx_restored_types:                  0
% 8.08/1.49  sat_num_of_epr_types:                   0
% 8.08/1.49  sat_num_of_non_cyclic_types:            0
% 8.08/1.49  sat_guarded_non_collapsed_types:        0
% 8.08/1.49  num_pure_diseq_elim:                    0
% 8.08/1.49  simp_replaced_by:                       0
% 8.08/1.49  res_preprocessed:                       89
% 8.08/1.49  prep_upred:                             0
% 8.08/1.49  prep_unflattend:                        2
% 8.08/1.49  smt_new_axioms:                         0
% 8.08/1.49  pred_elim_cands:                        5
% 8.08/1.49  pred_elim:                              0
% 8.08/1.49  pred_elim_cl:                           0
% 8.08/1.49  pred_elim_cycles:                       1
% 8.08/1.49  merged_defs:                            0
% 8.08/1.49  merged_defs_ncl:                        0
% 8.08/1.49  bin_hyper_res:                          0
% 8.08/1.49  prep_cycles:                            3
% 8.08/1.49  pred_elim_time:                         0.001
% 8.08/1.49  splitting_time:                         0.
% 8.08/1.49  sem_filter_time:                        0.
% 8.08/1.49  monotx_time:                            0.001
% 8.08/1.49  subtype_inf_time:                       0.
% 8.08/1.49  
% 8.08/1.49  ------ Problem properties
% 8.08/1.49  
% 8.08/1.49  clauses:                                22
% 8.08/1.49  conjectures:                            6
% 8.08/1.49  epr:                                    2
% 8.08/1.49  horn:                                   18
% 8.08/1.49  ground:                                 6
% 8.08/1.49  unary:                                  3
% 8.08/1.49  binary:                                 7
% 8.08/1.49  lits:                                   61
% 8.08/1.49  lits_eq:                                7
% 8.08/1.49  fd_pure:                                0
% 8.08/1.49  fd_pseudo:                              0
% 8.08/1.49  fd_cond:                                0
% 8.08/1.49  fd_pseudo_cond:                         2
% 8.08/1.49  ac_symbols:                             0
% 8.08/1.49  
% 8.08/1.49  ------ Propositional Solver
% 8.08/1.49  
% 8.08/1.49  prop_solver_calls:                      26
% 8.08/1.49  prop_fast_solver_calls:                 2171
% 8.08/1.49  smt_solver_calls:                       0
% 8.08/1.49  smt_fast_solver_calls:                  0
% 8.08/1.49  prop_num_of_clauses:                    10697
% 8.08/1.49  prop_preprocess_simplified:             18463
% 8.08/1.49  prop_fo_subsumed:                       250
% 8.08/1.49  prop_solver_time:                       0.
% 8.08/1.49  smt_solver_time:                        0.
% 8.08/1.49  smt_fast_solver_time:                   0.
% 8.08/1.49  prop_fast_solver_time:                  0.
% 8.08/1.49  prop_unsat_core_time:                   0.001
% 8.08/1.49  
% 8.08/1.49  ------ QBF
% 8.08/1.49  
% 8.08/1.49  qbf_q_res:                              0
% 8.08/1.49  qbf_num_tautologies:                    0
% 8.08/1.49  qbf_prep_cycles:                        0
% 8.08/1.49  
% 8.08/1.49  ------ BMC1
% 8.08/1.49  
% 8.08/1.49  bmc1_current_bound:                     -1
% 8.08/1.49  bmc1_last_solved_bound:                 -1
% 8.08/1.49  bmc1_unsat_core_size:                   -1
% 8.08/1.49  bmc1_unsat_core_parents_size:           -1
% 8.08/1.49  bmc1_merge_next_fun:                    0
% 8.08/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.08/1.49  
% 8.08/1.49  ------ Instantiation
% 8.08/1.49  
% 8.08/1.49  inst_num_of_clauses:                    3138
% 8.08/1.49  inst_num_in_passive:                    981
% 8.08/1.49  inst_num_in_active:                     1374
% 8.08/1.49  inst_num_in_unprocessed:                782
% 8.08/1.49  inst_num_of_loops:                      1671
% 8.08/1.49  inst_num_of_learning_restarts:          0
% 8.08/1.49  inst_num_moves_active_passive:          292
% 8.08/1.49  inst_lit_activity:                      0
% 8.08/1.49  inst_lit_activity_moves:                0
% 8.08/1.49  inst_num_tautologies:                   0
% 8.08/1.49  inst_num_prop_implied:                  0
% 8.08/1.49  inst_num_existing_simplified:           0
% 8.08/1.49  inst_num_eq_res_simplified:             0
% 8.08/1.49  inst_num_child_elim:                    0
% 8.08/1.49  inst_num_of_dismatching_blockings:      4686
% 8.08/1.49  inst_num_of_non_proper_insts:           5781
% 8.08/1.49  inst_num_of_duplicates:                 0
% 8.08/1.49  inst_inst_num_from_inst_to_res:         0
% 8.08/1.49  inst_dismatching_checking_time:         0.
% 8.08/1.49  
% 8.08/1.49  ------ Resolution
% 8.08/1.49  
% 8.08/1.49  res_num_of_clauses:                     0
% 8.08/1.49  res_num_in_passive:                     0
% 8.08/1.49  res_num_in_active:                      0
% 8.08/1.49  res_num_of_loops:                       92
% 8.08/1.49  res_forward_subset_subsumed:            424
% 8.08/1.49  res_backward_subset_subsumed:           0
% 8.08/1.49  res_forward_subsumed:                   0
% 8.08/1.49  res_backward_subsumed:                  0
% 8.08/1.49  res_forward_subsumption_resolution:     0
% 8.08/1.49  res_backward_subsumption_resolution:    0
% 8.08/1.49  res_clause_to_clause_subsumption:       2935
% 8.08/1.49  res_orphan_elimination:                 0
% 8.08/1.49  res_tautology_del:                      351
% 8.08/1.49  res_num_eq_res_simplified:              0
% 8.08/1.49  res_num_sel_changes:                    0
% 8.08/1.49  res_moves_from_active_to_pass:          0
% 8.08/1.49  
% 8.08/1.49  ------ Superposition
% 8.08/1.49  
% 8.08/1.49  sup_time_total:                         0.
% 8.08/1.49  sup_time_generating:                    0.
% 8.08/1.49  sup_time_sim_full:                      0.
% 8.08/1.49  sup_time_sim_immed:                     0.
% 8.08/1.49  
% 8.08/1.49  sup_num_of_clauses:                     766
% 8.08/1.49  sup_num_in_active:                      283
% 8.08/1.49  sup_num_in_passive:                     483
% 8.08/1.49  sup_num_of_loops:                       334
% 8.08/1.49  sup_fw_superposition:                   589
% 8.08/1.49  sup_bw_superposition:                   716
% 8.08/1.49  sup_immediate_simplified:               395
% 8.08/1.49  sup_given_eliminated:                   0
% 8.08/1.49  comparisons_done:                       0
% 8.08/1.49  comparisons_avoided:                    0
% 8.08/1.49  
% 8.08/1.49  ------ Simplifications
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  sim_fw_subset_subsumed:                 66
% 8.08/1.49  sim_bw_subset_subsumed:                 103
% 8.08/1.49  sim_fw_subsumed:                        50
% 8.08/1.49  sim_bw_subsumed:                        1
% 8.08/1.49  sim_fw_subsumption_res:                 9
% 8.08/1.49  sim_bw_subsumption_res:                 5
% 8.08/1.49  sim_tautology_del:                      65
% 8.08/1.49  sim_eq_tautology_del:                   74
% 8.08/1.49  sim_eq_res_simp:                        0
% 8.08/1.49  sim_fw_demodulated:                     3
% 8.08/1.49  sim_bw_demodulated:                     36
% 8.08/1.49  sim_light_normalised:                   327
% 8.08/1.49  sim_joinable_taut:                      0
% 8.08/1.49  sim_joinable_simp:                      0
% 8.08/1.49  sim_ac_normalised:                      0
% 8.08/1.49  sim_smt_subsumption:                    0
% 8.08/1.49  
%------------------------------------------------------------------------------
