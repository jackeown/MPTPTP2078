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
% DateTime   : Thu Dec  3 12:18:08 EST 2020

% Result     : Theorem 20.18s
% Output     : CNFRefutation 20.18s
% Verified   : 
% Statistics : Number of formulae       :  313 (9339 expanded)
%              Number of clauses        :  227 (3686 expanded)
%              Number of leaves         :   26 (1693 expanded)
%              Depth                    :   34
%              Number of atoms          : 1113 (43529 expanded)
%              Number of equality atoms :  496 (6461 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f22,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f62,plain,(
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
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f63,plain,(
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
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f65,plain,(
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
     => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          | ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v2_compts_1(sK5,X0) )
        & ( ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(sK5,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
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
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
            | ~ v2_compts_1(X1,sK4) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
              & v2_compts_1(X1,sK4) ) ) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
      | ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v2_compts_1(sK5,sK4) )
    & ( ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        & v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
      | ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
        & v2_compts_1(sK5,sK4) ) )
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f63,f65,f64])).

fof(f105,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_compts_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    ! [X2,X0] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f94,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f30,f47])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f85,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f106,plain,
    ( v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_compts_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f111,plain,(
    ! [X2,X0] :
      ( k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f110,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_compts_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_75251,plain,
    ( ~ v2_compts_1(sK5,X0)
    | v2_compts_1(sK5,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_76463,plain,
    ( ~ v2_compts_1(sK5,X0)
    | v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_75251])).

cnf(c_78330,plain,
    ( ~ v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
    | v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_76463])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3198,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3198,c_4])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3174,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6565,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3209,c_3174])).

cnf(c_25,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3180,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14715,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6565,c_3180])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3164,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_29,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3177,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4050,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3177,c_3182])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3196,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5820,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4050,c_3196])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3884,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3177,c_3181])).

cnf(c_19878,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5820,c_3884])).

cnf(c_19879,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19878])).

cnf(c_19886,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(superposition,[status(thm)],[c_3164,c_19879])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3175,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_19957,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19886,c_3175])).

cnf(c_65,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3572,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3574,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_3572])).

cnf(c_7094,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_19958,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19886,c_3175])).

cnf(c_20035,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19958])).

cnf(c_20998,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19957,c_42,c_65,c_3574,c_7094,c_20035])).

cnf(c_20999,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0 ),
    inference(renaming,[status(thm)],[c_20998])).

cnf(c_21006,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
    inference(equality_resolution,[status(thm)],[c_20999])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3168,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_22371,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21006,c_3168])).

cnf(c_39,negated_conjecture,
    ( v2_compts_1(sK5,sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3167,plain,
    ( v2_compts_1(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3172,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4941,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | v2_compts_1(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_3172])).

cnf(c_45,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5523,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_compts_1(sK5,sK4) = iProver_top
    | g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4941,c_45])).

cnf(c_5524,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | v2_compts_1(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5523])).

cnf(c_23813,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | v2_compts_1(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_22371,c_5524])).

cnf(c_3579,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3581,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_3579])).

cnf(c_3686,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3687,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3686])).

cnf(c_2407,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3767,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_3829,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3831,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_3829])).

cnf(c_2409,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3660,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK4))
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_3766,plain,
    ( m1_subset_1(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK4))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3660])).

cnf(c_8857,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK4))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3766])).

cnf(c_13138,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != k1_zfmisc_1(u1_struct_0(sK4))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_8857])).

cnf(c_13139,plain,
    ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != k1_zfmisc_1(u1_struct_0(sK4))
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13138])).

cnf(c_2411,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4637,plain,
    ( X0 != u1_struct_0(sK4)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2411])).

cnf(c_5432,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4637])).

cnf(c_13796,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5432])).

cnf(c_5424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | X1 = u1_struct_0(sK4)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_9202,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | X0 = u1_struct_0(sK4)
    | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_5424])).

cnf(c_14905,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_9202])).

cnf(c_25022,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23813,c_42,c_45,c_65,c_3574,c_3581,c_3687,c_3767,c_3831,c_13139,c_13796,c_14905,c_22371])).

cnf(c_33,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3173,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_25025,plain,
    ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
    | m1_pre_topc(X0,k1_pre_topc(sK4,sK5)) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25022,c_3173])).

cnf(c_3633,plain,
    ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3634,plain,
    ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3633])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4029,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK4,sK5),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4030,plain,
    ( m1_pre_topc(k1_pre_topc(sK4,sK5),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4029])).

cnf(c_4032,plain,
    ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4030])).

cnf(c_27095,plain,
    ( m1_pre_topc(X0,k1_pre_topc(sK4,sK5)) = iProver_top
    | m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25025,c_45,c_3634,c_4032,c_22371])).

cnf(c_27096,plain,
    ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
    | m1_pre_topc(X0,k1_pre_topc(sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_27095])).

cnf(c_27108,plain,
    ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
    | m1_pre_topc(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0)),k1_pre_topc(sK4,sK5)) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14715,c_27096])).

cnf(c_64,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_66,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_3573,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3572])).

cnf(c_3575,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3573])).

cnf(c_4015,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_4016,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4015])).

cnf(c_4566,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_4567,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4566])).

cnf(c_4886,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4887,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4886])).

cnf(c_4889,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) != iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4887])).

cnf(c_57126,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0)),k1_pre_topc(sK4,sK5)) = iProver_top
    | m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27108,c_42,c_45,c_65,c_66,c_3574,c_3575,c_3581,c_3767,c_3831,c_4016,c_4567,c_4889,c_13139,c_13796,c_14905,c_22371])).

cnf(c_57127,plain,
    ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
    | m1_pre_topc(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0)),k1_pre_topc(sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_57126])).

cnf(c_23811,plain,
    ( m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22371,c_3174])).

cnf(c_24728,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23811,c_3174])).

cnf(c_67,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27898,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24728,c_67])).

cnf(c_27899,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_27898])).

cnf(c_57138,plain,
    ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
    | m1_pre_topc(sK4,k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_57127,c_27899])).

cnf(c_3619,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4099,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) ),
    inference(instantiation,[status(thm)],[c_3619])).

cnf(c_4102,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4099])).

cnf(c_2408,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_4161,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_2408])).

cnf(c_5550,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4161])).

cnf(c_8063,plain,
    ( k2_struct_0(k1_pre_topc(sK4,sK5)) != sK5
    | sK5 = k2_struct_0(k1_pre_topc(sK4,sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5550])).

cnf(c_27,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_488,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_27,c_22])).

cnf(c_9116,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK4,sK5))
    | k2_struct_0(k1_pre_topc(sK4,sK5)) = u1_struct_0(k1_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_9118,plain,
    ( k2_struct_0(k1_pre_topc(sK4,sK5)) = u1_struct_0(k1_pre_topc(sK4,sK5))
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9116])).

cnf(c_3918,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_12607,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_3918])).

cnf(c_5624,plain,
    ( X0 != X1
    | X0 = k2_struct_0(k1_pre_topc(sK4,sK5))
    | k2_struct_0(k1_pre_topc(sK4,sK5)) != X1 ),
    inference(instantiation,[status(thm)],[c_2408])).

cnf(c_9115,plain,
    ( X0 = k2_struct_0(k1_pre_topc(sK4,sK5))
    | X0 != u1_struct_0(k1_pre_topc(sK4,sK5))
    | k2_struct_0(k1_pre_topc(sK4,sK5)) != u1_struct_0(k1_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_5624])).

cnf(c_16277,plain,
    ( k2_struct_0(k1_pre_topc(sK4,sK5)) != u1_struct_0(k1_pre_topc(sK4,sK5))
    | k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) = k2_struct_0(k1_pre_topc(sK4,sK5))
    | k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != u1_struct_0(k1_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_9115])).

cnf(c_5481,plain,
    ( k2_subset_1(u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_16278,plain,
    ( k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) = u1_struct_0(k1_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_5481])).

cnf(c_6936,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_3180])).

cnf(c_7276,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6936,c_45,c_66,c_3575])).

cnf(c_7277,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7276])).

cnf(c_3178,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7282,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7277,c_3178])).

cnf(c_7283,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7277,c_3173])).

cnf(c_7788,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7283,c_45])).

cnf(c_7789,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7788])).

cnf(c_7794,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7789,c_3178])).

cnf(c_7970,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7282,c_45,c_7794])).

cnf(c_7971,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7970])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_25])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_269,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_26])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_3162,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_4117,plain,
    ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3209,c_3162])).

cnf(c_7977,plain,
    ( k2_struct_0(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)))) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7971,c_4117])).

cnf(c_9548,plain,
    ( k2_struct_0(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)))) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
    | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7977,c_3162])).

cnf(c_3638,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_7297,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7283])).

cnf(c_3161,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_7979,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7971,c_3161])).

cnf(c_8693,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
    | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7979,c_3162])).

cnf(c_17445,plain,
    ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
    | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8693,c_45])).

cnf(c_17446,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
    | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
    inference(renaming,[status(thm)],[c_17445])).

cnf(c_4115,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_3162])).

cnf(c_4570,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4115,c_45,c_66,c_3575])).

cnf(c_4571,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4570])).

cnf(c_6938,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4571,c_3180])).

cnf(c_7779,plain,
    ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top
    | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6938,c_45])).

cnf(c_7780,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_7779])).

cnf(c_7785,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7780,c_3178])).

cnf(c_8579,plain,
    ( l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top
    | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7785,c_45])).

cnf(c_8580,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8579])).

cnf(c_19,plain,
    ( ~ v2_pre_topc(X0)
    | sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3185,plain,
    ( v2_pre_topc(X0) != iProver_top
    | sP0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8587,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | v2_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top
    | sP0(k1_pre_topc(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8580,c_3185])).

cnf(c_4007,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_4011,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4007])).

cnf(c_16727,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8587,c_42,c_45,c_65,c_66,c_3574,c_3575,c_3581,c_3767,c_3831,c_4011,c_4571,c_13139,c_13796,c_14905])).

cnf(c_17447,plain,
    ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_17446,c_16727])).

cnf(c_17466,plain,
    ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17447,c_6565])).

cnf(c_17906,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17466])).

cnf(c_17908,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_17906])).

cnf(c_19808,plain,
    ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9548,c_42,c_3638,c_7297,c_17908])).

cnf(c_11779,plain,
    ( X0 != k2_struct_0(k1_pre_topc(sK4,sK5))
    | sK5 = X0
    | sK5 != k2_struct_0(k1_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4161])).

cnf(c_40608,plain,
    ( k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != k2_struct_0(k1_pre_topc(sK4,sK5))
    | sK5 != k2_struct_0(k1_pre_topc(sK4,sK5))
    | sK5 = k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_11779])).

cnf(c_3650,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_3917,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
    | X0 != k2_subset_1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3650])).

cnf(c_4449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | X0 != k2_subset_1(u1_struct_0(X1))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_3917])).

cnf(c_59329,plain,
    ( ~ m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))
    | sK5 != k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_4449])).

cnf(c_59330,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))
    | sK5 != k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5)))
    | m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59329])).

cnf(c_59661,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_57138,c_42,c_45,c_3634,c_3638,c_3767,c_4032,c_4102,c_7297,c_8063,c_9118,c_12607,c_16277,c_16278,c_17908,c_22371,c_40608,c_59330])).

cnf(c_59671,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK4,sK5),sK5),k1_pre_topc(sK4,sK5)) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_59661,c_3180])).

cnf(c_61956,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK4,sK5),sK5),k1_pre_topc(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59671,c_45,c_3634,c_4032,c_22371])).

cnf(c_3171,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3438,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3171,c_3174])).

cnf(c_24724,plain,
    ( v2_compts_1(sK5,X0) != iProver_top
    | v2_compts_1(sK5,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23811,c_3438])).

cnf(c_28836,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_compts_1(sK5,X1) = iProver_top
    | v2_compts_1(sK5,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24724,c_67])).

cnf(c_28837,plain,
    ( v2_compts_1(sK5,X0) != iProver_top
    | v2_compts_1(sK5,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_28836])).

cnf(c_61961,plain,
    ( v2_compts_1(sK5,k1_pre_topc(k1_pre_topc(sK4,sK5),sK5)) != iProver_top
    | v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
    | m1_pre_topc(sK4,k1_pre_topc(k1_pre_topc(sK4,sK5),sK5)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_61956,c_28837])).

cnf(c_41,negated_conjecture,
    ( v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_compts_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_46,plain,
    ( v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v2_compts_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4008,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4009,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4008])).

cnf(c_4144,plain,
    ( k1_pre_topc(sK4,sK5) = k1_pre_topc(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_5330,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_2419,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4556,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | X0 != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | X1 != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_2419])).

cnf(c_5329,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | X0 != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_4556])).

cnf(c_13187,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | k1_pre_topc(sK4,sK5) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_5329])).

cnf(c_13196,plain,
    ( k1_pre_topc(sK4,sK5) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13187])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X0)
    | k1_pre_topc(X1,k2_struct_0(X0)) = X0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3195,plain,
    ( k1_pre_topc(X0,k2_struct_0(X1)) = X1
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16767,plain,
    ( k1_pre_topc(X0,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16727,c_3195])).

cnf(c_16768,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = k1_pre_topc(X0,sK5)
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16767,c_16727])).

cnf(c_16770,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = k1_pre_topc(sK4,sK5)
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16768])).

cnf(c_36,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3738,plain,
    ( ~ v2_compts_1(sK5,X0)
    | v2_compts_1(sK5,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_5347,plain,
    ( v2_compts_1(sK5,X0)
    | ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_3738])).

cnf(c_23881,plain,
    ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
    | ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_5347])).

cnf(c_23884,plain,
    ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
    | v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23881])).

cnf(c_5400,plain,
    ( X0 != X1
    | k1_pre_topc(sK4,sK5) != X1
    | k1_pre_topc(sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_2408])).

cnf(c_9010,plain,
    ( X0 != k1_pre_topc(sK4,sK5)
    | k1_pre_topc(sK4,sK5) = X0
    | k1_pre_topc(sK4,sK5) != k1_pre_topc(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5400])).

cnf(c_14618,plain,
    ( k1_pre_topc(X0,sK5) != k1_pre_topc(sK4,sK5)
    | k1_pre_topc(sK4,sK5) = k1_pre_topc(X0,sK5)
    | k1_pre_topc(sK4,sK5) != k1_pre_topc(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_9010])).

cnf(c_30471,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != k1_pre_topc(sK4,sK5)
    | k1_pre_topc(sK4,sK5) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | k1_pre_topc(sK4,sK5) != k1_pre_topc(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_14618])).

cnf(c_3170,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3426,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3170,c_3174])).

cnf(c_59674,plain,
    ( v2_compts_1(sK5,X0) != iProver_top
    | v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK4,sK5),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_59661,c_3426])).

cnf(c_59735,plain,
    ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
    | v2_compts_1(sK5,sK4) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59674])).

cnf(c_62201,plain,
    ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_61961,c_42,c_45,c_46,c_65,c_66,c_3574,c_3575,c_3581,c_3634,c_3638,c_3767,c_3831,c_4009,c_4016,c_4032,c_4102,c_4144,c_4567,c_5330,c_7297,c_8063,c_9118,c_12607,c_13139,c_13196,c_13796,c_14905,c_16277,c_16278,c_16770,c_17908,c_22371,c_23884,c_30471,c_40608,c_59330,c_59735])).

cnf(c_62203,plain,
    ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_62201])).

cnf(c_59669,plain,
    ( v2_compts_1(sK5,X0) = iProver_top
    | v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK4,sK5),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_59661,c_3438])).

cnf(c_59728,plain,
    ( v2_compts_1(sK5,X0)
    | ~ v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
    | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),X0)
    | ~ l1_pre_topc(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_59669])).

cnf(c_59730,plain,
    ( ~ v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
    | v2_compts_1(sK5,sK4)
    | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_59728])).

cnf(c_22460,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22371])).

cnf(c_37,negated_conjecture,
    ( ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_compts_1(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f110])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78330,c_62203,c_59730,c_59329,c_40608,c_30471,c_22460,c_22371,c_19808,c_16770,c_16278,c_16277,c_14905,c_13796,c_13187,c_13139,c_13138,c_12607,c_9118,c_8063,c_5330,c_4567,c_4144,c_4099,c_4032,c_4016,c_4015,c_4009,c_3831,c_3767,c_3634,c_3633,c_3581,c_3575,c_3574,c_66,c_65,c_37,c_45,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:14:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 20.18/3.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.18/3.02  
% 20.18/3.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 20.18/3.02  
% 20.18/3.02  ------  iProver source info
% 20.18/3.02  
% 20.18/3.02  git: date: 2020-06-30 10:37:57 +0100
% 20.18/3.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 20.18/3.02  git: non_committed_changes: false
% 20.18/3.02  git: last_make_outside_of_git: false
% 20.18/3.02  
% 20.18/3.02  ------ 
% 20.18/3.02  
% 20.18/3.02  ------ Input Options
% 20.18/3.02  
% 20.18/3.02  --out_options                           all
% 20.18/3.02  --tptp_safe_out                         true
% 20.18/3.02  --problem_path                          ""
% 20.18/3.02  --include_path                          ""
% 20.18/3.02  --clausifier                            res/vclausify_rel
% 20.18/3.02  --clausifier_options                    --mode clausify
% 20.18/3.02  --stdin                                 false
% 20.18/3.02  --stats_out                             all
% 20.18/3.02  
% 20.18/3.02  ------ General Options
% 20.18/3.02  
% 20.18/3.02  --fof                                   false
% 20.18/3.02  --time_out_real                         305.
% 20.18/3.02  --time_out_virtual                      -1.
% 20.18/3.02  --symbol_type_check                     false
% 20.18/3.02  --clausify_out                          false
% 20.18/3.02  --sig_cnt_out                           false
% 20.18/3.02  --trig_cnt_out                          false
% 20.18/3.02  --trig_cnt_out_tolerance                1.
% 20.18/3.02  --trig_cnt_out_sk_spl                   false
% 20.18/3.02  --abstr_cl_out                          false
% 20.18/3.02  
% 20.18/3.02  ------ Global Options
% 20.18/3.02  
% 20.18/3.02  --schedule                              default
% 20.18/3.02  --add_important_lit                     false
% 20.18/3.02  --prop_solver_per_cl                    1000
% 20.18/3.02  --min_unsat_core                        false
% 20.18/3.02  --soft_assumptions                      false
% 20.18/3.02  --soft_lemma_size                       3
% 20.18/3.02  --prop_impl_unit_size                   0
% 20.18/3.02  --prop_impl_unit                        []
% 20.18/3.02  --share_sel_clauses                     true
% 20.18/3.02  --reset_solvers                         false
% 20.18/3.02  --bc_imp_inh                            [conj_cone]
% 20.18/3.02  --conj_cone_tolerance                   3.
% 20.18/3.02  --extra_neg_conj                        none
% 20.18/3.02  --large_theory_mode                     true
% 20.18/3.02  --prolific_symb_bound                   200
% 20.18/3.02  --lt_threshold                          2000
% 20.18/3.02  --clause_weak_htbl                      true
% 20.18/3.02  --gc_record_bc_elim                     false
% 20.18/3.02  
% 20.18/3.02  ------ Preprocessing Options
% 20.18/3.02  
% 20.18/3.02  --preprocessing_flag                    true
% 20.18/3.02  --time_out_prep_mult                    0.1
% 20.18/3.02  --splitting_mode                        input
% 20.18/3.02  --splitting_grd                         true
% 20.18/3.02  --splitting_cvd                         false
% 20.18/3.02  --splitting_cvd_svl                     false
% 20.18/3.02  --splitting_nvd                         32
% 20.18/3.02  --sub_typing                            true
% 20.18/3.02  --prep_gs_sim                           true
% 20.18/3.02  --prep_unflatten                        true
% 20.18/3.02  --prep_res_sim                          true
% 20.18/3.02  --prep_upred                            true
% 20.18/3.02  --prep_sem_filter                       exhaustive
% 20.18/3.02  --prep_sem_filter_out                   false
% 20.18/3.02  --pred_elim                             true
% 20.18/3.02  --res_sim_input                         true
% 20.18/3.02  --eq_ax_congr_red                       true
% 20.18/3.02  --pure_diseq_elim                       true
% 20.18/3.02  --brand_transform                       false
% 20.18/3.02  --non_eq_to_eq                          false
% 20.18/3.02  --prep_def_merge                        true
% 20.18/3.02  --prep_def_merge_prop_impl              false
% 20.18/3.02  --prep_def_merge_mbd                    true
% 20.18/3.02  --prep_def_merge_tr_red                 false
% 20.18/3.02  --prep_def_merge_tr_cl                  false
% 20.18/3.02  --smt_preprocessing                     true
% 20.18/3.02  --smt_ac_axioms                         fast
% 20.18/3.02  --preprocessed_out                      false
% 20.18/3.02  --preprocessed_stats                    false
% 20.18/3.02  
% 20.18/3.02  ------ Abstraction refinement Options
% 20.18/3.02  
% 20.18/3.02  --abstr_ref                             []
% 20.18/3.02  --abstr_ref_prep                        false
% 20.18/3.02  --abstr_ref_until_sat                   false
% 20.18/3.02  --abstr_ref_sig_restrict                funpre
% 20.18/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 20.18/3.02  --abstr_ref_under                       []
% 20.18/3.02  
% 20.18/3.02  ------ SAT Options
% 20.18/3.02  
% 20.18/3.02  --sat_mode                              false
% 20.18/3.02  --sat_fm_restart_options                ""
% 20.18/3.02  --sat_gr_def                            false
% 20.18/3.02  --sat_epr_types                         true
% 20.18/3.02  --sat_non_cyclic_types                  false
% 20.18/3.02  --sat_finite_models                     false
% 20.18/3.02  --sat_fm_lemmas                         false
% 20.18/3.02  --sat_fm_prep                           false
% 20.18/3.02  --sat_fm_uc_incr                        true
% 20.18/3.02  --sat_out_model                         small
% 20.18/3.02  --sat_out_clauses                       false
% 20.18/3.02  
% 20.18/3.02  ------ QBF Options
% 20.18/3.02  
% 20.18/3.02  --qbf_mode                              false
% 20.18/3.02  --qbf_elim_univ                         false
% 20.18/3.02  --qbf_dom_inst                          none
% 20.18/3.02  --qbf_dom_pre_inst                      false
% 20.18/3.02  --qbf_sk_in                             false
% 20.18/3.02  --qbf_pred_elim                         true
% 20.18/3.02  --qbf_split                             512
% 20.18/3.02  
% 20.18/3.02  ------ BMC1 Options
% 20.18/3.02  
% 20.18/3.02  --bmc1_incremental                      false
% 20.18/3.02  --bmc1_axioms                           reachable_all
% 20.18/3.02  --bmc1_min_bound                        0
% 20.18/3.02  --bmc1_max_bound                        -1
% 20.18/3.02  --bmc1_max_bound_default                -1
% 20.18/3.02  --bmc1_symbol_reachability              true
% 20.18/3.02  --bmc1_property_lemmas                  false
% 20.18/3.02  --bmc1_k_induction                      false
% 20.18/3.02  --bmc1_non_equiv_states                 false
% 20.18/3.02  --bmc1_deadlock                         false
% 20.18/3.02  --bmc1_ucm                              false
% 20.18/3.02  --bmc1_add_unsat_core                   none
% 20.18/3.02  --bmc1_unsat_core_children              false
% 20.18/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 20.18/3.02  --bmc1_out_stat                         full
% 20.18/3.02  --bmc1_ground_init                      false
% 20.18/3.02  --bmc1_pre_inst_next_state              false
% 20.18/3.02  --bmc1_pre_inst_state                   false
% 20.18/3.02  --bmc1_pre_inst_reach_state             false
% 20.18/3.02  --bmc1_out_unsat_core                   false
% 20.18/3.02  --bmc1_aig_witness_out                  false
% 20.18/3.02  --bmc1_verbose                          false
% 20.18/3.02  --bmc1_dump_clauses_tptp                false
% 20.18/3.02  --bmc1_dump_unsat_core_tptp             false
% 20.18/3.02  --bmc1_dump_file                        -
% 20.18/3.02  --bmc1_ucm_expand_uc_limit              128
% 20.18/3.02  --bmc1_ucm_n_expand_iterations          6
% 20.18/3.02  --bmc1_ucm_extend_mode                  1
% 20.18/3.02  --bmc1_ucm_init_mode                    2
% 20.18/3.02  --bmc1_ucm_cone_mode                    none
% 20.18/3.02  --bmc1_ucm_reduced_relation_type        0
% 20.18/3.02  --bmc1_ucm_relax_model                  4
% 20.18/3.02  --bmc1_ucm_full_tr_after_sat            true
% 20.18/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 20.18/3.02  --bmc1_ucm_layered_model                none
% 20.18/3.02  --bmc1_ucm_max_lemma_size               10
% 20.18/3.02  
% 20.18/3.02  ------ AIG Options
% 20.18/3.02  
% 20.18/3.02  --aig_mode                              false
% 20.18/3.02  
% 20.18/3.02  ------ Instantiation Options
% 20.18/3.02  
% 20.18/3.02  --instantiation_flag                    true
% 20.18/3.02  --inst_sos_flag                         false
% 20.18/3.02  --inst_sos_phase                        true
% 20.18/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.18/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.18/3.02  --inst_lit_sel_side                     num_symb
% 20.18/3.02  --inst_solver_per_active                1400
% 20.18/3.02  --inst_solver_calls_frac                1.
% 20.18/3.02  --inst_passive_queue_type               priority_queues
% 20.18/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.18/3.02  --inst_passive_queues_freq              [25;2]
% 20.18/3.02  --inst_dismatching                      true
% 20.18/3.02  --inst_eager_unprocessed_to_passive     true
% 20.18/3.02  --inst_prop_sim_given                   true
% 20.18/3.02  --inst_prop_sim_new                     false
% 20.18/3.02  --inst_subs_new                         false
% 20.18/3.02  --inst_eq_res_simp                      false
% 20.18/3.02  --inst_subs_given                       false
% 20.18/3.02  --inst_orphan_elimination               true
% 20.18/3.02  --inst_learning_loop_flag               true
% 20.18/3.02  --inst_learning_start                   3000
% 20.18/3.02  --inst_learning_factor                  2
% 20.18/3.02  --inst_start_prop_sim_after_learn       3
% 20.18/3.02  --inst_sel_renew                        solver
% 20.18/3.02  --inst_lit_activity_flag                true
% 20.18/3.02  --inst_restr_to_given                   false
% 20.18/3.02  --inst_activity_threshold               500
% 20.18/3.02  --inst_out_proof                        true
% 20.18/3.02  
% 20.18/3.02  ------ Resolution Options
% 20.18/3.02  
% 20.18/3.02  --resolution_flag                       true
% 20.18/3.02  --res_lit_sel                           adaptive
% 20.18/3.02  --res_lit_sel_side                      none
% 20.18/3.02  --res_ordering                          kbo
% 20.18/3.02  --res_to_prop_solver                    active
% 20.18/3.02  --res_prop_simpl_new                    false
% 20.18/3.02  --res_prop_simpl_given                  true
% 20.18/3.02  --res_passive_queue_type                priority_queues
% 20.18/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.18/3.02  --res_passive_queues_freq               [15;5]
% 20.18/3.02  --res_forward_subs                      full
% 20.18/3.02  --res_backward_subs                     full
% 20.18/3.02  --res_forward_subs_resolution           true
% 20.18/3.02  --res_backward_subs_resolution          true
% 20.18/3.02  --res_orphan_elimination                true
% 20.18/3.02  --res_time_limit                        2.
% 20.18/3.02  --res_out_proof                         true
% 20.18/3.02  
% 20.18/3.02  ------ Superposition Options
% 20.18/3.02  
% 20.18/3.02  --superposition_flag                    true
% 20.18/3.02  --sup_passive_queue_type                priority_queues
% 20.18/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.18/3.02  --sup_passive_queues_freq               [8;1;4]
% 20.18/3.02  --demod_completeness_check              fast
% 20.18/3.02  --demod_use_ground                      true
% 20.18/3.02  --sup_to_prop_solver                    passive
% 20.18/3.02  --sup_prop_simpl_new                    true
% 20.18/3.02  --sup_prop_simpl_given                  true
% 20.18/3.02  --sup_fun_splitting                     false
% 20.18/3.02  --sup_smt_interval                      50000
% 20.18/3.02  
% 20.18/3.02  ------ Superposition Simplification Setup
% 20.18/3.02  
% 20.18/3.02  --sup_indices_passive                   []
% 20.18/3.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.18/3.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.18/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.18/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 20.18/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.18/3.02  --sup_full_bw                           [BwDemod]
% 20.18/3.02  --sup_immed_triv                        [TrivRules]
% 20.18/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.18/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.18/3.02  --sup_immed_bw_main                     []
% 20.18/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.18/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 20.18/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.18/3.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.18/3.02  
% 20.18/3.02  ------ Combination Options
% 20.18/3.02  
% 20.18/3.02  --comb_res_mult                         3
% 20.18/3.02  --comb_sup_mult                         2
% 20.18/3.02  --comb_inst_mult                        10
% 20.18/3.02  
% 20.18/3.02  ------ Debug Options
% 20.18/3.02  
% 20.18/3.02  --dbg_backtrace                         false
% 20.18/3.02  --dbg_dump_prop_clauses                 false
% 20.18/3.02  --dbg_dump_prop_clauses_file            -
% 20.18/3.02  --dbg_out_stat                          false
% 20.18/3.02  ------ Parsing...
% 20.18/3.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 20.18/3.02  
% 20.18/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 20.18/3.02  
% 20.18/3.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 20.18/3.02  
% 20.18/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 20.18/3.02  ------ Proving...
% 20.18/3.02  ------ Problem Properties 
% 20.18/3.02  
% 20.18/3.02  
% 20.18/3.02  clauses                                 43
% 20.18/3.02  conjectures                             7
% 20.18/3.02  EPR                                     8
% 20.18/3.02  Horn                                    31
% 20.18/3.02  unary                                   4
% 20.18/3.02  binary                                  13
% 20.18/3.02  lits                                    130
% 20.18/3.02  lits eq                                 10
% 20.18/3.02  fd_pure                                 0
% 20.18/3.02  fd_pseudo                               0
% 20.18/3.02  fd_cond                                 0
% 20.18/3.02  fd_pseudo_cond                          2
% 20.18/3.02  AC symbols                              0
% 20.18/3.02  
% 20.18/3.02  ------ Schedule dynamic 5 is on 
% 20.18/3.02  
% 20.18/3.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 20.18/3.02  
% 20.18/3.02  
% 20.18/3.02  ------ 
% 20.18/3.02  Current options:
% 20.18/3.02  ------ 
% 20.18/3.02  
% 20.18/3.02  ------ Input Options
% 20.18/3.02  
% 20.18/3.02  --out_options                           all
% 20.18/3.02  --tptp_safe_out                         true
% 20.18/3.02  --problem_path                          ""
% 20.18/3.02  --include_path                          ""
% 20.18/3.02  --clausifier                            res/vclausify_rel
% 20.18/3.02  --clausifier_options                    --mode clausify
% 20.18/3.02  --stdin                                 false
% 20.18/3.02  --stats_out                             all
% 20.18/3.02  
% 20.18/3.02  ------ General Options
% 20.18/3.02  
% 20.18/3.02  --fof                                   false
% 20.18/3.02  --time_out_real                         305.
% 20.18/3.02  --time_out_virtual                      -1.
% 20.18/3.02  --symbol_type_check                     false
% 20.18/3.02  --clausify_out                          false
% 20.18/3.02  --sig_cnt_out                           false
% 20.18/3.02  --trig_cnt_out                          false
% 20.18/3.02  --trig_cnt_out_tolerance                1.
% 20.18/3.02  --trig_cnt_out_sk_spl                   false
% 20.18/3.02  --abstr_cl_out                          false
% 20.18/3.02  
% 20.18/3.02  ------ Global Options
% 20.18/3.02  
% 20.18/3.02  --schedule                              default
% 20.18/3.02  --add_important_lit                     false
% 20.18/3.02  --prop_solver_per_cl                    1000
% 20.18/3.02  --min_unsat_core                        false
% 20.18/3.02  --soft_assumptions                      false
% 20.18/3.02  --soft_lemma_size                       3
% 20.18/3.02  --prop_impl_unit_size                   0
% 20.18/3.02  --prop_impl_unit                        []
% 20.18/3.02  --share_sel_clauses                     true
% 20.18/3.02  --reset_solvers                         false
% 20.18/3.02  --bc_imp_inh                            [conj_cone]
% 20.18/3.02  --conj_cone_tolerance                   3.
% 20.18/3.02  --extra_neg_conj                        none
% 20.18/3.02  --large_theory_mode                     true
% 20.18/3.02  --prolific_symb_bound                   200
% 20.18/3.02  --lt_threshold                          2000
% 20.18/3.02  --clause_weak_htbl                      true
% 20.18/3.02  --gc_record_bc_elim                     false
% 20.18/3.02  
% 20.18/3.02  ------ Preprocessing Options
% 20.18/3.02  
% 20.18/3.02  --preprocessing_flag                    true
% 20.18/3.02  --time_out_prep_mult                    0.1
% 20.18/3.02  --splitting_mode                        input
% 20.18/3.02  --splitting_grd                         true
% 20.18/3.02  --splitting_cvd                         false
% 20.18/3.02  --splitting_cvd_svl                     false
% 20.18/3.02  --splitting_nvd                         32
% 20.18/3.02  --sub_typing                            true
% 20.18/3.02  --prep_gs_sim                           true
% 20.18/3.02  --prep_unflatten                        true
% 20.18/3.02  --prep_res_sim                          true
% 20.18/3.02  --prep_upred                            true
% 20.18/3.02  --prep_sem_filter                       exhaustive
% 20.18/3.02  --prep_sem_filter_out                   false
% 20.18/3.02  --pred_elim                             true
% 20.18/3.02  --res_sim_input                         true
% 20.18/3.02  --eq_ax_congr_red                       true
% 20.18/3.02  --pure_diseq_elim                       true
% 20.18/3.02  --brand_transform                       false
% 20.18/3.02  --non_eq_to_eq                          false
% 20.18/3.02  --prep_def_merge                        true
% 20.18/3.02  --prep_def_merge_prop_impl              false
% 20.18/3.02  --prep_def_merge_mbd                    true
% 20.18/3.02  --prep_def_merge_tr_red                 false
% 20.18/3.02  --prep_def_merge_tr_cl                  false
% 20.18/3.02  --smt_preprocessing                     true
% 20.18/3.02  --smt_ac_axioms                         fast
% 20.18/3.02  --preprocessed_out                      false
% 20.18/3.02  --preprocessed_stats                    false
% 20.18/3.02  
% 20.18/3.02  ------ Abstraction refinement Options
% 20.18/3.02  
% 20.18/3.02  --abstr_ref                             []
% 20.18/3.02  --abstr_ref_prep                        false
% 20.18/3.02  --abstr_ref_until_sat                   false
% 20.18/3.02  --abstr_ref_sig_restrict                funpre
% 20.18/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 20.18/3.02  --abstr_ref_under                       []
% 20.18/3.02  
% 20.18/3.02  ------ SAT Options
% 20.18/3.02  
% 20.18/3.02  --sat_mode                              false
% 20.18/3.02  --sat_fm_restart_options                ""
% 20.18/3.02  --sat_gr_def                            false
% 20.18/3.02  --sat_epr_types                         true
% 20.18/3.02  --sat_non_cyclic_types                  false
% 20.18/3.02  --sat_finite_models                     false
% 20.18/3.02  --sat_fm_lemmas                         false
% 20.18/3.02  --sat_fm_prep                           false
% 20.18/3.02  --sat_fm_uc_incr                        true
% 20.18/3.02  --sat_out_model                         small
% 20.18/3.02  --sat_out_clauses                       false
% 20.18/3.02  
% 20.18/3.02  ------ QBF Options
% 20.18/3.02  
% 20.18/3.02  --qbf_mode                              false
% 20.18/3.02  --qbf_elim_univ                         false
% 20.18/3.02  --qbf_dom_inst                          none
% 20.18/3.02  --qbf_dom_pre_inst                      false
% 20.18/3.02  --qbf_sk_in                             false
% 20.18/3.02  --qbf_pred_elim                         true
% 20.18/3.02  --qbf_split                             512
% 20.18/3.02  
% 20.18/3.02  ------ BMC1 Options
% 20.18/3.02  
% 20.18/3.02  --bmc1_incremental                      false
% 20.18/3.02  --bmc1_axioms                           reachable_all
% 20.18/3.02  --bmc1_min_bound                        0
% 20.18/3.02  --bmc1_max_bound                        -1
% 20.18/3.02  --bmc1_max_bound_default                -1
% 20.18/3.02  --bmc1_symbol_reachability              true
% 20.18/3.02  --bmc1_property_lemmas                  false
% 20.18/3.02  --bmc1_k_induction                      false
% 20.18/3.02  --bmc1_non_equiv_states                 false
% 20.18/3.02  --bmc1_deadlock                         false
% 20.18/3.02  --bmc1_ucm                              false
% 20.18/3.02  --bmc1_add_unsat_core                   none
% 20.18/3.02  --bmc1_unsat_core_children              false
% 20.18/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 20.18/3.02  --bmc1_out_stat                         full
% 20.18/3.02  --bmc1_ground_init                      false
% 20.18/3.02  --bmc1_pre_inst_next_state              false
% 20.18/3.02  --bmc1_pre_inst_state                   false
% 20.18/3.02  --bmc1_pre_inst_reach_state             false
% 20.18/3.02  --bmc1_out_unsat_core                   false
% 20.18/3.02  --bmc1_aig_witness_out                  false
% 20.18/3.02  --bmc1_verbose                          false
% 20.18/3.02  --bmc1_dump_clauses_tptp                false
% 20.18/3.02  --bmc1_dump_unsat_core_tptp             false
% 20.18/3.02  --bmc1_dump_file                        -
% 20.18/3.02  --bmc1_ucm_expand_uc_limit              128
% 20.18/3.02  --bmc1_ucm_n_expand_iterations          6
% 20.18/3.02  --bmc1_ucm_extend_mode                  1
% 20.18/3.02  --bmc1_ucm_init_mode                    2
% 20.18/3.02  --bmc1_ucm_cone_mode                    none
% 20.18/3.02  --bmc1_ucm_reduced_relation_type        0
% 20.18/3.02  --bmc1_ucm_relax_model                  4
% 20.18/3.02  --bmc1_ucm_full_tr_after_sat            true
% 20.18/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 20.18/3.02  --bmc1_ucm_layered_model                none
% 20.18/3.02  --bmc1_ucm_max_lemma_size               10
% 20.18/3.02  
% 20.18/3.02  ------ AIG Options
% 20.18/3.02  
% 20.18/3.02  --aig_mode                              false
% 20.18/3.02  
% 20.18/3.02  ------ Instantiation Options
% 20.18/3.02  
% 20.18/3.02  --instantiation_flag                    true
% 20.18/3.02  --inst_sos_flag                         false
% 20.18/3.02  --inst_sos_phase                        true
% 20.18/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.18/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.18/3.02  --inst_lit_sel_side                     none
% 20.18/3.02  --inst_solver_per_active                1400
% 20.18/3.02  --inst_solver_calls_frac                1.
% 20.18/3.02  --inst_passive_queue_type               priority_queues
% 20.18/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.18/3.02  --inst_passive_queues_freq              [25;2]
% 20.18/3.02  --inst_dismatching                      true
% 20.18/3.02  --inst_eager_unprocessed_to_passive     true
% 20.18/3.02  --inst_prop_sim_given                   true
% 20.18/3.02  --inst_prop_sim_new                     false
% 20.18/3.02  --inst_subs_new                         false
% 20.18/3.02  --inst_eq_res_simp                      false
% 20.18/3.02  --inst_subs_given                       false
% 20.18/3.02  --inst_orphan_elimination               true
% 20.18/3.02  --inst_learning_loop_flag               true
% 20.18/3.02  --inst_learning_start                   3000
% 20.18/3.02  --inst_learning_factor                  2
% 20.18/3.02  --inst_start_prop_sim_after_learn       3
% 20.18/3.02  --inst_sel_renew                        solver
% 20.18/3.02  --inst_lit_activity_flag                true
% 20.18/3.02  --inst_restr_to_given                   false
% 20.18/3.02  --inst_activity_threshold               500
% 20.18/3.02  --inst_out_proof                        true
% 20.18/3.02  
% 20.18/3.02  ------ Resolution Options
% 20.18/3.02  
% 20.18/3.02  --resolution_flag                       false
% 20.18/3.02  --res_lit_sel                           adaptive
% 20.18/3.02  --res_lit_sel_side                      none
% 20.18/3.02  --res_ordering                          kbo
% 20.18/3.02  --res_to_prop_solver                    active
% 20.18/3.02  --res_prop_simpl_new                    false
% 20.18/3.02  --res_prop_simpl_given                  true
% 20.18/3.02  --res_passive_queue_type                priority_queues
% 20.18/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.18/3.02  --res_passive_queues_freq               [15;5]
% 20.18/3.02  --res_forward_subs                      full
% 20.18/3.02  --res_backward_subs                     full
% 20.18/3.02  --res_forward_subs_resolution           true
% 20.18/3.02  --res_backward_subs_resolution          true
% 20.18/3.02  --res_orphan_elimination                true
% 20.18/3.02  --res_time_limit                        2.
% 20.18/3.02  --res_out_proof                         true
% 20.18/3.02  
% 20.18/3.02  ------ Superposition Options
% 20.18/3.02  
% 20.18/3.02  --superposition_flag                    true
% 20.18/3.02  --sup_passive_queue_type                priority_queues
% 20.18/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.18/3.02  --sup_passive_queues_freq               [8;1;4]
% 20.18/3.02  --demod_completeness_check              fast
% 20.18/3.02  --demod_use_ground                      true
% 20.18/3.02  --sup_to_prop_solver                    passive
% 20.18/3.02  --sup_prop_simpl_new                    true
% 20.18/3.02  --sup_prop_simpl_given                  true
% 20.18/3.02  --sup_fun_splitting                     false
% 20.18/3.02  --sup_smt_interval                      50000
% 20.18/3.02  
% 20.18/3.02  ------ Superposition Simplification Setup
% 20.18/3.02  
% 20.18/3.02  --sup_indices_passive                   []
% 20.18/3.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.18/3.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.18/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.18/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 20.18/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.18/3.02  --sup_full_bw                           [BwDemod]
% 20.18/3.02  --sup_immed_triv                        [TrivRules]
% 20.18/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.18/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.18/3.02  --sup_immed_bw_main                     []
% 20.18/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.18/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 20.18/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 20.18/3.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 20.18/3.02  
% 20.18/3.02  ------ Combination Options
% 20.18/3.02  
% 20.18/3.02  --comb_res_mult                         3
% 20.18/3.02  --comb_sup_mult                         2
% 20.18/3.02  --comb_inst_mult                        10
% 20.18/3.02  
% 20.18/3.02  ------ Debug Options
% 20.18/3.02  
% 20.18/3.02  --dbg_backtrace                         false
% 20.18/3.02  --dbg_dump_prop_clauses                 false
% 20.18/3.02  --dbg_dump_prop_clauses_file            -
% 20.18/3.02  --dbg_out_stat                          false
% 20.18/3.02  
% 20.18/3.02  
% 20.18/3.02  
% 20.18/3.02  
% 20.18/3.02  ------ Proving...
% 20.18/3.02  
% 20.18/3.02  
% 20.18/3.02  % SZS status Theorem for theBenchmark.p
% 20.18/3.02  
% 20.18/3.02  % SZS output start CNFRefutation for theBenchmark.p
% 20.18/3.02  
% 20.18/3.02  fof(f18,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f43,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f18])).
% 20.18/3.02  
% 20.18/3.02  fof(f44,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f43])).
% 20.18/3.02  
% 20.18/3.02  fof(f61,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(nnf_transformation,[],[f44])).
% 20.18/3.02  
% 20.18/3.02  fof(f103,plain,(
% 20.18/3.02    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f61])).
% 20.18/3.02  
% 20.18/3.02  fof(f114,plain,(
% 20.18/3.02    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(equality_resolution,[],[f103])).
% 20.18/3.02  
% 20.18/3.02  fof(f3,axiom,(
% 20.18/3.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f72,plain,(
% 20.18/3.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 20.18/3.02    inference(cnf_transformation,[],[f3])).
% 20.18/3.02  
% 20.18/3.02  fof(f2,axiom,(
% 20.18/3.02    ! [X0] : k2_subset_1(X0) = X0),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f71,plain,(
% 20.18/3.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 20.18/3.02    inference(cnf_transformation,[],[f2])).
% 20.18/3.02  
% 20.18/3.02  fof(f15,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f39,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f15])).
% 20.18/3.02  
% 20.18/3.02  fof(f99,plain,(
% 20.18/3.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f39])).
% 20.18/3.02  
% 20.18/3.02  fof(f10,axiom,(
% 20.18/3.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f33,plain,(
% 20.18/3.02    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 20.18/3.02    inference(ennf_transformation,[],[f10])).
% 20.18/3.02  
% 20.18/3.02  fof(f34,plain,(
% 20.18/3.02    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f33])).
% 20.18/3.02  
% 20.18/3.02  fof(f93,plain,(
% 20.18/3.02    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f34])).
% 20.18/3.02  
% 20.18/3.02  fof(f19,conjecture,(
% 20.18/3.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f20,negated_conjecture,(
% 20.18/3.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 20.18/3.02    inference(negated_conjecture,[],[f19])).
% 20.18/3.02  
% 20.18/3.02  fof(f22,plain,(
% 20.18/3.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 20.18/3.02    inference(pure_predicate_removal,[],[f20])).
% 20.18/3.02  
% 20.18/3.02  fof(f45,plain,(
% 20.18/3.02    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 20.18/3.02    inference(ennf_transformation,[],[f22])).
% 20.18/3.02  
% 20.18/3.02  fof(f46,plain,(
% 20.18/3.02    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f45])).
% 20.18/3.02  
% 20.18/3.02  fof(f62,plain,(
% 20.18/3.02    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 20.18/3.02    inference(nnf_transformation,[],[f46])).
% 20.18/3.02  
% 20.18/3.02  fof(f63,plain,(
% 20.18/3.02    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f62])).
% 20.18/3.02  
% 20.18/3.02  fof(f65,plain,(
% 20.18/3.02    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) => ((~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(sK5,X0)) & ((m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(sK5,X0))))) )),
% 20.18/3.02    introduced(choice_axiom,[])).
% 20.18/3.02  
% 20.18/3.02  fof(f64,plain,(
% 20.18/3.02    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_compts_1(X1,sK4)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v2_compts_1(X1,sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 20.18/3.02    introduced(choice_axiom,[])).
% 20.18/3.02  
% 20.18/3.02  fof(f66,plain,(
% 20.18/3.02    ((~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_compts_1(sK5,sK4)) & ((m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) & v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v2_compts_1(sK5,sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 20.18/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f63,f65,f64])).
% 20.18/3.02  
% 20.18/3.02  fof(f105,plain,(
% 20.18/3.02    l1_pre_topc(sK4)),
% 20.18/3.02    inference(cnf_transformation,[],[f66])).
% 20.18/3.02  
% 20.18/3.02  fof(f13,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f37,plain,(
% 20.18/3.02    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f13])).
% 20.18/3.02  
% 20.18/3.02  fof(f96,plain,(
% 20.18/3.02    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f37])).
% 20.18/3.02  
% 20.18/3.02  fof(f9,axiom,(
% 20.18/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f32,plain,(
% 20.18/3.02    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 20.18/3.02    inference(ennf_transformation,[],[f9])).
% 20.18/3.02  
% 20.18/3.02  fof(f91,plain,(
% 20.18/3.02    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 20.18/3.02    inference(cnf_transformation,[],[f32])).
% 20.18/3.02  
% 20.18/3.02  fof(f5,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f25,plain,(
% 20.18/3.02    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f5])).
% 20.18/3.02  
% 20.18/3.02  fof(f26,plain,(
% 20.18/3.02    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f25])).
% 20.18/3.02  
% 20.18/3.02  fof(f74,plain,(
% 20.18/3.02    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f26])).
% 20.18/3.02  
% 20.18/3.02  fof(f90,plain,(
% 20.18/3.02    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 20.18/3.02    inference(cnf_transformation,[],[f32])).
% 20.18/3.02  
% 20.18/3.02  fof(f14,axiom,(
% 20.18/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f38,plain,(
% 20.18/3.02    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 20.18/3.02    inference(ennf_transformation,[],[f14])).
% 20.18/3.02  
% 20.18/3.02  fof(f97,plain,(
% 20.18/3.02    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 20.18/3.02    inference(cnf_transformation,[],[f38])).
% 20.18/3.02  
% 20.18/3.02  fof(f109,plain,(
% 20.18/3.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 20.18/3.02    inference(cnf_transformation,[],[f66])).
% 20.18/3.02  
% 20.18/3.02  fof(f108,plain,(
% 20.18/3.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | v2_compts_1(sK5,sK4)),
% 20.18/3.02    inference(cnf_transformation,[],[f66])).
% 20.18/3.02  
% 20.18/3.02  fof(f17,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f41,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f17])).
% 20.18/3.02  
% 20.18/3.02  fof(f42,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f41])).
% 20.18/3.02  
% 20.18/3.02  fof(f101,plain,(
% 20.18/3.02    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f42])).
% 20.18/3.02  
% 20.18/3.02  fof(f113,plain,(
% 20.18/3.02    ( ! [X2,X0] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(equality_resolution,[],[f101])).
% 20.18/3.02  
% 20.18/3.02  fof(f16,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f40,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f16])).
% 20.18/3.02  
% 20.18/3.02  fof(f100,plain,(
% 20.18/3.02    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f40])).
% 20.18/3.02  
% 20.18/3.02  fof(f12,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f36,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f12])).
% 20.18/3.02  
% 20.18/3.02  fof(f95,plain,(
% 20.18/3.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f36])).
% 20.18/3.02  
% 20.18/3.02  fof(f11,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f35,plain,(
% 20.18/3.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f11])).
% 20.18/3.02  
% 20.18/3.02  fof(f94,plain,(
% 20.18/3.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f35])).
% 20.18/3.02  
% 20.18/3.02  fof(f8,axiom,(
% 20.18/3.02    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f31,plain,(
% 20.18/3.02    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f8])).
% 20.18/3.02  
% 20.18/3.02  fof(f89,plain,(
% 20.18/3.02    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f31])).
% 20.18/3.02  
% 20.18/3.02  fof(f6,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f27,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f6])).
% 20.18/3.02  
% 20.18/3.02  fof(f28,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f27])).
% 20.18/3.02  
% 20.18/3.02  fof(f50,plain,(
% 20.18/3.02    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(nnf_transformation,[],[f28])).
% 20.18/3.02  
% 20.18/3.02  fof(f75,plain,(
% 20.18/3.02    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f50])).
% 20.18/3.02  
% 20.18/3.02  fof(f112,plain,(
% 20.18/3.02    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(equality_resolution,[],[f75])).
% 20.18/3.02  
% 20.18/3.02  fof(f92,plain,(
% 20.18/3.02    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f34])).
% 20.18/3.02  
% 20.18/3.02  fof(f7,axiom,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 20.18/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 20.18/3.02  
% 20.18/3.02  fof(f21,plain,(
% 20.18/3.02    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 20.18/3.02    inference(rectify,[],[f7])).
% 20.18/3.02  
% 20.18/3.02  fof(f29,plain,(
% 20.18/3.02    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(ennf_transformation,[],[f21])).
% 20.18/3.02  
% 20.18/3.02  fof(f30,plain,(
% 20.18/3.02    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f29])).
% 20.18/3.02  
% 20.18/3.02  fof(f47,plain,(
% 20.18/3.02    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 20.18/3.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 20.18/3.02  
% 20.18/3.02  fof(f48,plain,(
% 20.18/3.02    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(definition_folding,[],[f30,f47])).
% 20.18/3.02  
% 20.18/3.02  fof(f56,plain,(
% 20.18/3.02    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(nnf_transformation,[],[f48])).
% 20.18/3.02  
% 20.18/3.02  fof(f57,plain,(
% 20.18/3.02    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(flattening,[],[f56])).
% 20.18/3.02  
% 20.18/3.02  fof(f58,plain,(
% 20.18/3.02    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(rectify,[],[f57])).
% 20.18/3.02  
% 20.18/3.02  fof(f59,plain,(
% 20.18/3.02    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 20.18/3.02    introduced(choice_axiom,[])).
% 20.18/3.02  
% 20.18/3.02  fof(f60,plain,(
% 20.18/3.02    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 20.18/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 20.18/3.02  
% 20.18/3.02  fof(f85,plain,(
% 20.18/3.02    ( ! [X0] : (sP0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f60])).
% 20.18/3.02  
% 20.18/3.02  fof(f106,plain,(
% 20.18/3.02    v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v2_compts_1(sK5,sK4)),
% 20.18/3.02    inference(cnf_transformation,[],[f66])).
% 20.18/3.02  
% 20.18/3.02  fof(f76,plain,(
% 20.18/3.02    ( ! [X2,X0,X1] : (k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f50])).
% 20.18/3.02  
% 20.18/3.02  fof(f111,plain,(
% 20.18/3.02    ( ! [X2,X0] : (k1_pre_topc(X0,k2_struct_0(X2)) = X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(equality_resolution,[],[f76])).
% 20.18/3.02  
% 20.18/3.02  fof(f102,plain,(
% 20.18/3.02    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(cnf_transformation,[],[f61])).
% 20.18/3.02  
% 20.18/3.02  fof(f115,plain,(
% 20.18/3.02    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 20.18/3.02    inference(equality_resolution,[],[f102])).
% 20.18/3.02  
% 20.18/3.02  fof(f110,plain,(
% 20.18/3.02    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v2_compts_1(sK5,sK4)),
% 20.18/3.02    inference(cnf_transformation,[],[f66])).
% 20.18/3.02  
% 20.18/3.02  cnf(c_35,plain,
% 20.18/3.02      ( ~ v2_compts_1(X0,X1)
% 20.18/3.02      | v2_compts_1(X0,X2)
% 20.18/3.02      | ~ m1_pre_topc(X1,X2)
% 20.18/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 20.18/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ l1_pre_topc(X2) ),
% 20.18/3.02      inference(cnf_transformation,[],[f114]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_75251,plain,
% 20.18/3.02      ( ~ v2_compts_1(sK5,X0)
% 20.18/3.02      | v2_compts_1(sK5,X1)
% 20.18/3.02      | ~ m1_pre_topc(X0,X1)
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ l1_pre_topc(X1) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_35]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_76463,plain,
% 20.18/3.02      ( ~ v2_compts_1(sK5,X0)
% 20.18/3.02      | v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.02      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_75251]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_78330,plain,
% 20.18/3.02      ( ~ v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
% 20.18/3.02      | v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.02      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_76463]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5,plain,
% 20.18/3.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 20.18/3.02      inference(cnf_transformation,[],[f72]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3198,plain,
% 20.18/3.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4,plain,
% 20.18/3.02      ( k2_subset_1(X0) = X0 ),
% 20.18/3.02      inference(cnf_transformation,[],[f71]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3209,plain,
% 20.18/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 20.18/3.02      inference(light_normalisation,[status(thm)],[c_3198,c_4]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_32,plain,
% 20.18/3.02      ( ~ m1_pre_topc(X0,X1)
% 20.18/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ l1_pre_topc(X1) ),
% 20.18/3.02      inference(cnf_transformation,[],[f99]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3174,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 20.18/3.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_6565,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3209,c_3174]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_25,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 20.18/3.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | ~ l1_pre_topc(X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f93]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3180,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 20.18/3.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_14715,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X0)),X1) = iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_6565,c_3180]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_42,negated_conjecture,
% 20.18/3.02      ( l1_pre_topc(sK4) ),
% 20.18/3.02      inference(cnf_transformation,[],[f105]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3164,plain,
% 20.18/3.02      ( l1_pre_topc(sK4) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_29,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 20.18/3.02      | ~ l1_pre_topc(X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f96]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3177,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_23,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 20.18/3.02      inference(cnf_transformation,[],[f91]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3182,plain,
% 20.18/3.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4050,plain,
% 20.18/3.02      ( l1_pre_topc(X0) != iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3177,c_3182]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7,plain,
% 20.18/3.02      ( ~ l1_pre_topc(X0)
% 20.18/3.02      | ~ v1_pre_topc(X0)
% 20.18/3.02      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 20.18/3.02      inference(cnf_transformation,[],[f74]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3196,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top
% 20.18/3.02      | v1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5820,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top
% 20.18/3.02      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_4050,c_3196]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_24,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 20.18/3.02      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 20.18/3.02      inference(cnf_transformation,[],[f90]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3181,plain,
% 20.18/3.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 20.18/3.02      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3884,plain,
% 20.18/3.02      ( l1_pre_topc(X0) != iProver_top
% 20.18/3.02      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3177,c_3181]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_19878,plain,
% 20.18/3.02      ( l1_pre_topc(X0) != iProver_top
% 20.18/3.02      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_5820,c_3884]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_19879,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_19878]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_19886,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3164,c_19879]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_31,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 20.18/3.02      | X2 = X1
% 20.18/3.02      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f97]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3175,plain,
% 20.18/3.02      ( X0 = X1
% 20.18/3.02      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 20.18/3.02      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_19957,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 20.18/3.02      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
% 20.18/3.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_19886,c_3175]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_65,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 20.18/3.02      | ~ l1_pre_topc(sK4) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_29]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3572,plain,
% 20.18/3.02      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_23]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3574,plain,
% 20.18/3.02      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3572]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7094,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 20.18/3.02      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_29]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_19958,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 20.18/3.02      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
% 20.18/3.02      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_19886,c_3175]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_20035,plain,
% 20.18/3.02      ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 20.18/3.02      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 20.18/3.02      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0 ),
% 20.18/3.02      inference(predicate_to_equality_rev,[status(thm)],[c_19958]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_20998,plain,
% 20.18/3.02      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
% 20.18/3.02      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1) ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_19957,c_42,c_65,c_3574,c_7094,c_20035]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_20999,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 20.18/3.02      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0 ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_20998]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_21006,plain,
% 20.18/3.02      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
% 20.18/3.02      inference(equality_resolution,[status(thm)],[c_20999]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_38,negated_conjecture,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 20.18/3.02      inference(cnf_transformation,[],[f109]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3168,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_22371,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(demodulation,[status(thm)],[c_21006,c_3168]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_39,negated_conjecture,
% 20.18/3.02      ( v2_compts_1(sK5,sK4)
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
% 20.18/3.02      inference(cnf_transformation,[],[f108]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3167,plain,
% 20.18/3.02      ( v2_compts_1(sK5,sK4) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_34,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 20.18/3.02      | ~ l1_pre_topc(X1)
% 20.18/3.02      | g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f113]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3172,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 20.18/3.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 20.18/3.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4941,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.02      | v2_compts_1(sK5,sK4) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3167,c_3172]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_45,plain,
% 20.18/3.02      ( l1_pre_topc(sK4) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5523,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 20.18/3.02      | v2_compts_1(sK5,sK4) = iProver_top
% 20.18/3.02      | g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_4941,c_45]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5524,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.02      | v2_compts_1(sK5,sK4) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_5523]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_23813,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.02      | v2_compts_1(sK5,sK4) = iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_22371,c_5524]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3579,plain,
% 20.18/3.02      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 20.18/3.02      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_24]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3581,plain,
% 20.18/3.02      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 20.18/3.02      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3579]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3686,plain,
% 20.18/3.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | ~ l1_pre_topc(sK4)
% 20.18/3.02      | g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_34]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3687,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_3686]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_2407,plain,( X0 = X0 ),theory(equality) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3767,plain,
% 20.18/3.02      ( sK5 = sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_2407]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3829,plain,
% 20.18/3.02      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 20.18/3.02      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 20.18/3.02      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_7]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3831,plain,
% 20.18/3.02      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3829]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_2409,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 20.18/3.02      theory(equality) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3660,plain,
% 20.18/3.02      ( m1_subset_1(X0,X1)
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | X1 != k1_zfmisc_1(u1_struct_0(sK4))
% 20.18/3.02      | X0 != sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_2409]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3766,plain,
% 20.18/3.02      ( m1_subset_1(sK5,X0)
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | X0 != k1_zfmisc_1(u1_struct_0(sK4))
% 20.18/3.02      | sK5 != sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3660]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_8857,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK4))
% 20.18/3.02      | sK5 != sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3766]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_13138,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != k1_zfmisc_1(u1_struct_0(sK4))
% 20.18/3.02      | sK5 != sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_8857]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_13139,plain,
% 20.18/3.02      ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != k1_zfmisc_1(u1_struct_0(sK4))
% 20.18/3.02      | sK5 != sK5
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_13138]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_2411,plain,
% 20.18/3.02      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 20.18/3.02      theory(equality) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4637,plain,
% 20.18/3.02      ( X0 != u1_struct_0(sK4)
% 20.18/3.02      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_2411]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5432,plain,
% 20.18/3.02      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 20.18/3.02      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_4637]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_13796,plain,
% 20.18/3.02      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
% 20.18/3.02      | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_5432]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5424,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 20.18/3.02      | X1 = u1_struct_0(sK4)
% 20.18/3.02      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK4),X0) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_31]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_9202,plain,
% 20.18/3.02      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 20.18/3.02      | X0 = u1_struct_0(sK4)
% 20.18/3.02      | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_5424]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_14905,plain,
% 20.18/3.02      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 20.18/3.02      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 20.18/3.02      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_9202]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_25022,plain,
% 20.18/3.02      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK4,sK5)),u1_pre_topc(k1_pre_topc(sK4,sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_23813,c_42,c_45,c_65,c_3574,c_3581,c_3687,c_3767,
% 20.18/3.02                 c_3831,c_13139,c_13796,c_14905,c_22371]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_33,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1)
% 20.18/3.02      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 20.18/3.02      | ~ l1_pre_topc(X1) ),
% 20.18/3.02      inference(cnf_transformation,[],[f100]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3173,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) = iProver_top
% 20.18/3.02      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_25025,plain,
% 20.18/3.02      ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
% 20.18/3.02      | m1_pre_topc(X0,k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_25022,c_3173]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3633,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4)
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | ~ l1_pre_topc(sK4) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_25]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3634,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_3633]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_28,plain,
% 20.18/3.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f95]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4029,plain,
% 20.18/3.02      ( ~ m1_pre_topc(k1_pre_topc(sK4,sK5),X0)
% 20.18/3.02      | ~ l1_pre_topc(X0)
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_28]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4030,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(sK4,sK5),X0) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_4029]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4032,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) != iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_4030]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_27095,plain,
% 20.18/3.02      ( m1_pre_topc(X0,k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_25025,c_45,c_3634,c_4032,c_22371]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_27096,plain,
% 20.18/3.02      ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
% 20.18/3.02      | m1_pre_topc(X0,k1_pre_topc(sK4,sK5)) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_27095]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_27108,plain,
% 20.18/3.02      ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0)),k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_14715,c_27096]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_64,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_66,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_64]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3573,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_3572]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3575,plain,
% 20.18/3.02      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3573]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4015,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.02      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_25]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4016,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_4015]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4566,plain,
% 20.18/3.02      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4)
% 20.18/3.02      | ~ l1_pre_topc(sK4) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_33]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4567,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_4566]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4886,plain,
% 20.18/3.02      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0)
% 20.18/3.02      | ~ l1_pre_topc(X0)
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_28]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4887,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_4886]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4889,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) != iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_4887]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_57126,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0)),k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_27108,c_42,c_45,c_65,c_66,c_3574,c_3575,c_3581,c_3767,
% 20.18/3.02                 c_3831,c_4016,c_4567,c_4889,c_13139,c_13796,c_14905,
% 20.18/3.02                 c_22371]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_57127,plain,
% 20.18/3.02      ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0)),k1_pre_topc(sK4,sK5)) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_57126]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_23811,plain,
% 20.18/3.02      ( m1_pre_topc(sK4,X0) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_22371,c_3174]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_24728,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | m1_pre_topc(sK4,X0) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_23811,c_3174]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_67,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_27898,plain,
% 20.18/3.02      ( l1_pre_topc(X1) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 20.18/3.02      | m1_pre_topc(sK4,X0) != iProver_top
% 20.18/3.02      | m1_pre_topc(X0,X1) != iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_24728,c_67]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_27899,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | m1_pre_topc(sK4,X0) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_27898]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_57138,plain,
% 20.18/3.02      ( m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top
% 20.18/3.02      | m1_pre_topc(sK4,k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(X0))) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_57127,c_27899]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3619,plain,
% 20.18/3.02      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_5]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4099,plain,
% 20.18/3.02      ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3619]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4102,plain,
% 20.18/3.02      ( m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_4099]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_2408,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4161,plain,
% 20.18/3.02      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_2408]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5550,plain,
% 20.18/3.02      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_4161]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_8063,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(sK4,sK5)) != sK5
% 20.18/3.02      | sK5 = k2_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | sK5 != sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_5550]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_27,plain,
% 20.18/3.02      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f94]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_22,plain,
% 20.18/3.02      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f89]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_488,plain,
% 20.18/3.02      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 20.18/3.02      inference(resolution,[status(thm)],[c_27,c_22]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_9116,plain,
% 20.18/3.02      ( ~ l1_pre_topc(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) = u1_struct_0(k1_pre_topc(sK4,sK5)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_488]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_9118,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(sK4,sK5)) = u1_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_9116]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3918,plain,
% 20.18/3.02      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_2407]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_12607,plain,
% 20.18/3.02      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3918]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5624,plain,
% 20.18/3.02      ( X0 != X1
% 20.18/3.02      | X0 = k2_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) != X1 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_2408]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_9115,plain,
% 20.18/3.02      ( X0 = k2_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | X0 != u1_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) != u1_struct_0(k1_pre_topc(sK4,sK5)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_5624]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_16277,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(sK4,sK5)) != u1_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) = k2_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != u1_struct_0(k1_pre_topc(sK4,sK5)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_9115]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_5481,plain,
% 20.18/3.02      ( k2_subset_1(u1_struct_0(X0)) = u1_struct_0(X0) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_4]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_16278,plain,
% 20.18/3.02      ( k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) = u1_struct_0(k1_pre_topc(sK4,sK5)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_5481]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_6936,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3168,c_3180]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7276,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_6936,c_45,c_66,c_3575]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7277,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_7276]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3178,plain,
% 20.18/3.02      ( m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7282,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7277,c_3178]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7283,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7277,c_3173]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7788,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_7283,c_45]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7789,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_7788]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7794,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7789,c_3178]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7970,plain,
% 20.18/3.02      ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_7282,c_45,c_7794]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7971,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_7970]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_9,plain,
% 20.18/3.02      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 20.18/3.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | ~ l1_pre_topc(X0)
% 20.18/3.02      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 20.18/3.02      inference(cnf_transformation,[],[f112]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_263,plain,
% 20.18/3.02      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | ~ l1_pre_topc(X0)
% 20.18/3.02      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_9,c_25]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_264,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ l1_pre_topc(X1)
% 20.18/3.02      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_263]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_26,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ l1_pre_topc(X1)
% 20.18/3.02      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 20.18/3.02      inference(cnf_transformation,[],[f92]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_269,plain,
% 20.18/3.02      ( ~ l1_pre_topc(X1)
% 20.18/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_264,c_26]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_270,plain,
% 20.18/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ l1_pre_topc(X1)
% 20.18/3.02      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_269]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3162,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 20.18/3.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4117,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3209,c_3162]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7977,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)))) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7971,c_4117]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_9548,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)))) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7977,c_3162]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3638,plain,
% 20.18/3.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | ~ l1_pre_topc(sK4)
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_270]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7297,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4)
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | ~ l1_pre_topc(sK4) ),
% 20.18/3.02      inference(predicate_to_equality_rev,[status(thm)],[c_7283]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3161,plain,
% 20.18/3.02      ( k2_struct_0(X0) = u1_struct_0(X0)
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7979,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7971,c_3161]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_8693,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7979,c_3162]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_17445,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
% 20.18/3.02      | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_8693,c_45]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_17446,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_17445]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4115,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_3168,c_3162]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4570,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 20.18/3.02      | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_4115,c_45,c_66,c_3575]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4571,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_4570]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_6938,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_4571,c_3180]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7779,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top
% 20.18/3.02      | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_6938,c_45]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7780,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_7779]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_7785,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_7780,c_3178]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_8579,plain,
% 20.18/3.02      ( l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_7785,c_45]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_8580,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) = iProver_top ),
% 20.18/3.02      inference(renaming,[status(thm)],[c_8579]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_19,plain,
% 20.18/3.02      ( ~ v2_pre_topc(X0) | sP0(X0) | ~ l1_pre_topc(X0) ),
% 20.18/3.02      inference(cnf_transformation,[],[f85]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3185,plain,
% 20.18/3.02      ( v2_pre_topc(X0) != iProver_top
% 20.18/3.02      | sP0(X0) = iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_8587,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | v2_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top
% 20.18/3.02      | sP0(k1_pre_topc(sK4,sK5)) = iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_8580,c_3185]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4007,plain,
% 20.18/3.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.02      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.02      | k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_270]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4011,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 20.18/3.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_4007]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_16727,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_8587,c_42,c_45,c_65,c_66,c_3574,c_3575,c_3581,c_3767,
% 20.18/3.02                 c_3831,c_4011,c_4571,c_13139,c_13796,c_14905]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_17447,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
% 20.18/3.02      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = sK5 ),
% 20.18/3.02      inference(light_normalisation,[status(thm)],[c_17446,c_16727]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_17466,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5
% 20.18/3.02      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_17447,c_6565]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_17906,plain,
% 20.18/3.02      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0)
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.02      | ~ l1_pre_topc(X0)
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
% 20.18/3.02      inference(predicate_to_equality_rev,[status(thm)],[c_17466]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_17908,plain,
% 20.18/3.02      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4)
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 20.18/3.02      | ~ l1_pre_topc(sK4)
% 20.18/3.02      | k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_17906]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_19808,plain,
% 20.18/3.02      ( k2_struct_0(k1_pre_topc(sK4,sK5)) = sK5 ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_9548,c_42,c_3638,c_7297,c_17908]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_11779,plain,
% 20.18/3.02      ( X0 != k2_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | sK5 = X0
% 20.18/3.02      | sK5 != k2_struct_0(k1_pre_topc(sK4,sK5)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_4161]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_40608,plain,
% 20.18/3.02      ( k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != k2_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | sK5 != k2_struct_0(k1_pre_topc(sK4,sK5))
% 20.18/3.02      | sK5 = k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_11779]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3650,plain,
% 20.18/3.02      ( m1_subset_1(X0,X1)
% 20.18/3.02      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 20.18/3.02      | X1 != k1_zfmisc_1(X2)
% 20.18/3.02      | X0 != k2_subset_1(X2) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_2409]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3917,plain,
% 20.18/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 20.18/3.02      | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
% 20.18/3.02      | X0 != k2_subset_1(X1)
% 20.18/3.02      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3650]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_4449,plain,
% 20.18/3.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | ~ m1_subset_1(k2_subset_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.02      | X0 != k2_subset_1(u1_struct_0(X1))
% 20.18/3.02      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_3917]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_59329,plain,
% 20.18/3.02      ( ~ m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
% 20.18/3.02      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))
% 20.18/3.02      | sK5 != k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))) ),
% 20.18/3.02      inference(instantiation,[status(thm)],[c_4449]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_59330,plain,
% 20.18/3.02      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))
% 20.18/3.02      | sK5 != k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5)))
% 20.18/3.02      | m1_subset_1(k2_subset_1(u1_struct_0(k1_pre_topc(sK4,sK5))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) != iProver_top
% 20.18/3.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_59329]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_59661,plain,
% 20.18/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) = iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_57138,c_42,c_45,c_3634,c_3638,c_3767,c_4032,c_4102,
% 20.18/3.02                 c_7297,c_8063,c_9118,c_12607,c_16277,c_16278,c_17908,
% 20.18/3.02                 c_22371,c_40608,c_59330]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_59671,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK4,sK5),sK5),k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.02      | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_59661,c_3180]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_61956,plain,
% 20.18/3.02      ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK4,sK5),sK5),k1_pre_topc(sK4,sK5)) = iProver_top ),
% 20.18/3.02      inference(global_propositional_subsumption,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_59671,c_45,c_3634,c_4032,c_22371]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3171,plain,
% 20.18/3.02      ( v2_compts_1(X0,X1) != iProver_top
% 20.18/3.02      | v2_compts_1(X0,X2) = iProver_top
% 20.18/3.02      | m1_pre_topc(X1,X2) != iProver_top
% 20.18/3.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 20.18/3.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 20.18/3.02      | l1_pre_topc(X2) != iProver_top ),
% 20.18/3.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_3438,plain,
% 20.18/3.02      ( v2_compts_1(X0,X1) != iProver_top
% 20.18/3.02      | v2_compts_1(X0,X2) = iProver_top
% 20.18/3.02      | m1_pre_topc(X1,X2) != iProver_top
% 20.18/3.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 20.18/3.02      | l1_pre_topc(X2) != iProver_top ),
% 20.18/3.02      inference(forward_subsumption_resolution,
% 20.18/3.02                [status(thm)],
% 20.18/3.02                [c_3171,c_3174]) ).
% 20.18/3.02  
% 20.18/3.02  cnf(c_24724,plain,
% 20.18/3.02      ( v2_compts_1(sK5,X0) != iProver_top
% 20.18/3.02      | v2_compts_1(sK5,X1) = iProver_top
% 20.18/3.02      | m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.02      | m1_pre_topc(sK4,X0) != iProver_top
% 20.18/3.02      | l1_pre_topc(X1) != iProver_top
% 20.18/3.02      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.02      inference(superposition,[status(thm)],[c_23811,c_3438]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_28836,plain,
% 20.18/3.03      ( l1_pre_topc(X1) != iProver_top
% 20.18/3.03      | m1_pre_topc(sK4,X0) != iProver_top
% 20.18/3.03      | m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.03      | v2_compts_1(sK5,X1) = iProver_top
% 20.18/3.03      | v2_compts_1(sK5,X0) != iProver_top ),
% 20.18/3.03      inference(global_propositional_subsumption,
% 20.18/3.03                [status(thm)],
% 20.18/3.03                [c_24724,c_67]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_28837,plain,
% 20.18/3.03      ( v2_compts_1(sK5,X0) != iProver_top
% 20.18/3.03      | v2_compts_1(sK5,X1) = iProver_top
% 20.18/3.03      | m1_pre_topc(X0,X1) != iProver_top
% 20.18/3.03      | m1_pre_topc(sK4,X0) != iProver_top
% 20.18/3.03      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.03      inference(renaming,[status(thm)],[c_28836]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_61961,plain,
% 20.18/3.03      ( v2_compts_1(sK5,k1_pre_topc(k1_pre_topc(sK4,sK5),sK5)) != iProver_top
% 20.18/3.03      | v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.03      | m1_pre_topc(sK4,k1_pre_topc(k1_pre_topc(sK4,sK5),sK5)) != iProver_top
% 20.18/3.03      | l1_pre_topc(k1_pre_topc(sK4,sK5)) != iProver_top ),
% 20.18/3.03      inference(superposition,[status(thm)],[c_61956,c_28837]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_41,negated_conjecture,
% 20.18/3.03      ( v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | v2_compts_1(sK5,sK4) ),
% 20.18/3.03      inference(cnf_transformation,[],[f106]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_46,plain,
% 20.18/3.03      ( v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 20.18/3.03      | v2_compts_1(sK5,sK4) = iProver_top ),
% 20.18/3.03      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_4008,plain,
% 20.18/3.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.03      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_26]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_4009,plain,
% 20.18/3.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 20.18/3.03      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 20.18/3.03      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) = iProver_top ),
% 20.18/3.03      inference(predicate_to_equality,[status(thm)],[c_4008]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_4144,plain,
% 20.18/3.03      ( k1_pre_topc(sK4,sK5) = k1_pre_topc(sK4,sK5) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_2407]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_5330,plain,
% 20.18/3.03      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_2407]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_2419,plain,
% 20.18/3.03      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 20.18/3.03      theory(equality) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_4556,plain,
% 20.18/3.03      ( m1_pre_topc(X0,X1)
% 20.18/3.03      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | X0 != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.03      | X1 != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_2419]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_5329,plain,
% 20.18/3.03      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | X0 != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.03      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_4556]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_13187,plain,
% 20.18/3.03      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | k1_pre_topc(sK4,sK5) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.03      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_5329]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_13196,plain,
% 20.18/3.03      ( k1_pre_topc(sK4,sK5) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.03      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 20.18/3.03      inference(predicate_to_equality,[status(thm)],[c_13187]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_8,plain,
% 20.18/3.03      ( ~ m1_pre_topc(X0,X1)
% 20.18/3.03      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.03      | ~ l1_pre_topc(X1)
% 20.18/3.03      | ~ v1_pre_topc(X0)
% 20.18/3.03      | k1_pre_topc(X1,k2_struct_0(X0)) = X0 ),
% 20.18/3.03      inference(cnf_transformation,[],[f111]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_3195,plain,
% 20.18/3.03      ( k1_pre_topc(X0,k2_struct_0(X1)) = X1
% 20.18/3.03      | m1_pre_topc(X1,X0) != iProver_top
% 20.18/3.03      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 20.18/3.03      | l1_pre_topc(X0) != iProver_top
% 20.18/3.03      | v1_pre_topc(X1) != iProver_top ),
% 20.18/3.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_16767,plain,
% 20.18/3.03      ( k1_pre_topc(X0,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
% 20.18/3.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 20.18/3.03      | l1_pre_topc(X0) != iProver_top
% 20.18/3.03      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
% 20.18/3.03      inference(superposition,[status(thm)],[c_16727,c_3195]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_16768,plain,
% 20.18/3.03      ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = k1_pre_topc(X0,sK5)
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),X0) != iProver_top
% 20.18/3.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 20.18/3.03      | l1_pre_topc(X0) != iProver_top
% 20.18/3.03      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
% 20.18/3.03      inference(light_normalisation,[status(thm)],[c_16767,c_16727]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_16770,plain,
% 20.18/3.03      ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = k1_pre_topc(sK4,sK5)
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5),sK4) != iProver_top
% 20.18/3.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 20.18/3.03      | l1_pre_topc(sK4) != iProver_top
% 20.18/3.03      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)) != iProver_top ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_16768]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_36,plain,
% 20.18/3.03      ( ~ v2_compts_1(X0,X1)
% 20.18/3.03      | v2_compts_1(X0,X2)
% 20.18/3.03      | ~ m1_pre_topc(X2,X1)
% 20.18/3.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 20.18/3.03      | ~ l1_pre_topc(X1) ),
% 20.18/3.03      inference(cnf_transformation,[],[f115]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_3738,plain,
% 20.18/3.03      ( ~ v2_compts_1(sK5,X0)
% 20.18/3.03      | v2_compts_1(sK5,X1)
% 20.18/3.03      | ~ m1_pre_topc(X1,X0)
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
% 20.18/3.03      | ~ l1_pre_topc(X0) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_36]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_5347,plain,
% 20.18/3.03      ( v2_compts_1(sK5,X0)
% 20.18/3.03      | ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.03      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_3738]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_23881,plain,
% 20.18/3.03      ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
% 20.18/3.03      | ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5))))
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.03      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_5347]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_23884,plain,
% 20.18/3.03      ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.03      | v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(sK4,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 20.18/3.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK4,sK5)))) != iProver_top
% 20.18/3.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 20.18/3.03      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 20.18/3.03      inference(predicate_to_equality,[status(thm)],[c_23881]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_5400,plain,
% 20.18/3.03      ( X0 != X1
% 20.18/3.03      | k1_pre_topc(sK4,sK5) != X1
% 20.18/3.03      | k1_pre_topc(sK4,sK5) = X0 ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_2408]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_9010,plain,
% 20.18/3.03      ( X0 != k1_pre_topc(sK4,sK5)
% 20.18/3.03      | k1_pre_topc(sK4,sK5) = X0
% 20.18/3.03      | k1_pre_topc(sK4,sK5) != k1_pre_topc(sK4,sK5) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_5400]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_14618,plain,
% 20.18/3.03      ( k1_pre_topc(X0,sK5) != k1_pre_topc(sK4,sK5)
% 20.18/3.03      | k1_pre_topc(sK4,sK5) = k1_pre_topc(X0,sK5)
% 20.18/3.03      | k1_pre_topc(sK4,sK5) != k1_pre_topc(sK4,sK5) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_9010]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_30471,plain,
% 20.18/3.03      ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != k1_pre_topc(sK4,sK5)
% 20.18/3.03      | k1_pre_topc(sK4,sK5) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 20.18/3.03      | k1_pre_topc(sK4,sK5) != k1_pre_topc(sK4,sK5) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_14618]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_3170,plain,
% 20.18/3.03      ( v2_compts_1(X0,X1) != iProver_top
% 20.18/3.03      | v2_compts_1(X0,X2) = iProver_top
% 20.18/3.03      | m1_pre_topc(X2,X1) != iProver_top
% 20.18/3.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 20.18/3.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 20.18/3.03      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_3426,plain,
% 20.18/3.03      ( v2_compts_1(X0,X1) != iProver_top
% 20.18/3.03      | v2_compts_1(X0,X2) = iProver_top
% 20.18/3.03      | m1_pre_topc(X2,X1) != iProver_top
% 20.18/3.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 20.18/3.03      | l1_pre_topc(X1) != iProver_top ),
% 20.18/3.03      inference(forward_subsumption_resolution,
% 20.18/3.03                [status(thm)],
% 20.18/3.03                [c_3170,c_3174]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_59674,plain,
% 20.18/3.03      ( v2_compts_1(sK5,X0) != iProver_top
% 20.18/3.03      | v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(sK4,sK5),X0) != iProver_top
% 20.18/3.03      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.03      inference(superposition,[status(thm)],[c_59661,c_3426]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_59735,plain,
% 20.18/3.03      ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top
% 20.18/3.03      | v2_compts_1(sK5,sK4) != iProver_top
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(sK4,sK5),sK4) != iProver_top
% 20.18/3.03      | l1_pre_topc(sK4) != iProver_top ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_59674]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_62201,plain,
% 20.18/3.03      ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) = iProver_top ),
% 20.18/3.03      inference(global_propositional_subsumption,
% 20.18/3.03                [status(thm)],
% 20.18/3.03                [c_61961,c_42,c_45,c_46,c_65,c_66,c_3574,c_3575,c_3581,
% 20.18/3.03                 c_3634,c_3638,c_3767,c_3831,c_4009,c_4016,c_4032,c_4102,
% 20.18/3.03                 c_4144,c_4567,c_5330,c_7297,c_8063,c_9118,c_12607,
% 20.18/3.03                 c_13139,c_13196,c_13796,c_14905,c_16277,c_16278,c_16770,
% 20.18/3.03                 c_17908,c_22371,c_23884,c_30471,c_40608,c_59330,c_59735]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_62203,plain,
% 20.18/3.03      ( v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) ),
% 20.18/3.03      inference(predicate_to_equality_rev,[status(thm)],[c_62201]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_59669,plain,
% 20.18/3.03      ( v2_compts_1(sK5,X0) = iProver_top
% 20.18/3.03      | v2_compts_1(sK5,k1_pre_topc(sK4,sK5)) != iProver_top
% 20.18/3.03      | m1_pre_topc(k1_pre_topc(sK4,sK5),X0) != iProver_top
% 20.18/3.03      | l1_pre_topc(X0) != iProver_top ),
% 20.18/3.03      inference(superposition,[status(thm)],[c_59661,c_3438]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_59728,plain,
% 20.18/3.03      ( v2_compts_1(sK5,X0)
% 20.18/3.03      | ~ v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
% 20.18/3.03      | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),X0)
% 20.18/3.03      | ~ l1_pre_topc(X0) ),
% 20.18/3.03      inference(predicate_to_equality_rev,[status(thm)],[c_59669]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_59730,plain,
% 20.18/3.03      ( ~ v2_compts_1(sK5,k1_pre_topc(sK4,sK5))
% 20.18/3.03      | v2_compts_1(sK5,sK4)
% 20.18/3.03      | ~ m1_pre_topc(k1_pre_topc(sK4,sK5),sK4)
% 20.18/3.03      | ~ l1_pre_topc(sK4) ),
% 20.18/3.03      inference(instantiation,[status(thm)],[c_59728]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_22460,plain,
% 20.18/3.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 20.18/3.03      inference(predicate_to_equality_rev,[status(thm)],[c_22371]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(c_37,negated_conjecture,
% 20.18/3.03      ( ~ v2_compts_1(sK5,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 20.18/3.03      | ~ v2_compts_1(sK5,sK4)
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
% 20.18/3.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 20.18/3.03      inference(cnf_transformation,[],[f110]) ).
% 20.18/3.03  
% 20.18/3.03  cnf(contradiction,plain,
% 20.18/3.03      ( $false ),
% 20.18/3.03      inference(minisat,
% 20.18/3.03                [status(thm)],
% 20.18/3.03                [c_78330,c_62203,c_59730,c_59329,c_40608,c_30471,c_22460,
% 20.18/3.03                 c_22371,c_19808,c_16770,c_16278,c_16277,c_14905,c_13796,
% 20.18/3.03                 c_13187,c_13139,c_13138,c_12607,c_9118,c_8063,c_5330,
% 20.18/3.03                 c_4567,c_4144,c_4099,c_4032,c_4016,c_4015,c_4009,c_3831,
% 20.18/3.03                 c_3767,c_3634,c_3633,c_3581,c_3575,c_3574,c_66,c_65,
% 20.18/3.03                 c_37,c_45,c_42]) ).
% 20.18/3.03  
% 20.18/3.03  
% 20.18/3.03  % SZS output end CNFRefutation for theBenchmark.p
% 20.18/3.03  
% 20.18/3.03  ------                               Statistics
% 20.18/3.03  
% 20.18/3.03  ------ General
% 20.18/3.03  
% 20.18/3.03  abstr_ref_over_cycles:                  0
% 20.18/3.03  abstr_ref_under_cycles:                 0
% 20.18/3.03  gc_basic_clause_elim:                   0
% 20.18/3.03  forced_gc_time:                         0
% 20.18/3.03  parsing_time:                           0.011
% 20.18/3.03  unif_index_cands_time:                  0.
% 20.18/3.03  unif_index_add_time:                    0.
% 20.18/3.03  orderings_time:                         0.
% 20.18/3.03  out_proof_time:                         0.033
% 20.18/3.03  total_time:                             2.345
% 20.18/3.03  num_of_symbols:                         56
% 20.18/3.03  num_of_terms:                           56587
% 20.18/3.03  
% 20.18/3.03  ------ Preprocessing
% 20.18/3.03  
% 20.18/3.03  num_of_splits:                          0
% 20.18/3.03  num_of_split_atoms:                     0
% 20.18/3.03  num_of_reused_defs:                     0
% 20.18/3.03  num_eq_ax_congr_red:                    19
% 20.18/3.03  num_of_sem_filtered_clauses:            1
% 20.18/3.03  num_of_subtypes:                        0
% 20.18/3.03  monotx_restored_types:                  0
% 20.18/3.03  sat_num_of_epr_types:                   0
% 20.18/3.03  sat_num_of_non_cyclic_types:            0
% 20.18/3.03  sat_guarded_non_collapsed_types:        0
% 20.18/3.03  num_pure_diseq_elim:                    0
% 20.18/3.03  simp_replaced_by:                       0
% 20.18/3.03  res_preprocessed:                       210
% 20.18/3.03  prep_upred:                             0
% 20.18/3.03  prep_unflattend:                        34
% 20.18/3.03  smt_new_axioms:                         0
% 20.18/3.03  pred_elim_cands:                        10
% 20.18/3.03  pred_elim:                              1
% 20.18/3.03  pred_elim_cl:                           1
% 20.18/3.03  pred_elim_cycles:                       9
% 20.18/3.03  merged_defs:                            0
% 20.18/3.03  merged_defs_ncl:                        0
% 20.18/3.03  bin_hyper_res:                          0
% 20.18/3.03  prep_cycles:                            4
% 20.18/3.03  pred_elim_time:                         0.046
% 20.18/3.03  splitting_time:                         0.
% 20.18/3.03  sem_filter_time:                        0.
% 20.18/3.03  monotx_time:                            0.001
% 20.18/3.03  subtype_inf_time:                       0.
% 20.18/3.03  
% 20.18/3.03  ------ Problem properties
% 20.18/3.03  
% 20.18/3.03  clauses:                                43
% 20.18/3.03  conjectures:                            7
% 20.18/3.03  epr:                                    8
% 20.18/3.03  horn:                                   31
% 20.18/3.03  ground:                                 7
% 20.18/3.03  unary:                                  4
% 20.18/3.03  binary:                                 13
% 20.18/3.03  lits:                                   130
% 20.18/3.03  lits_eq:                                10
% 20.18/3.03  fd_pure:                                0
% 20.18/3.03  fd_pseudo:                              0
% 20.18/3.03  fd_cond:                                0
% 20.18/3.03  fd_pseudo_cond:                         2
% 20.18/3.03  ac_symbols:                             0
% 20.18/3.03  
% 20.18/3.03  ------ Propositional Solver
% 20.18/3.03  
% 20.18/3.03  prop_solver_calls:                      38
% 20.18/3.03  prop_fast_solver_calls:                 4443
% 20.18/3.03  smt_solver_calls:                       0
% 20.18/3.03  smt_fast_solver_calls:                  0
% 20.18/3.03  prop_num_of_clauses:                    25078
% 20.18/3.03  prop_preprocess_simplified:             45531
% 20.18/3.03  prop_fo_subsumed:                       357
% 20.18/3.03  prop_solver_time:                       0.
% 20.18/3.03  smt_solver_time:                        0.
% 20.18/3.03  smt_fast_solver_time:                   0.
% 20.18/3.03  prop_fast_solver_time:                  0.
% 20.18/3.03  prop_unsat_core_time:                   0.003
% 20.18/3.03  
% 20.18/3.03  ------ QBF
% 20.18/3.03  
% 20.18/3.03  qbf_q_res:                              0
% 20.18/3.03  qbf_num_tautologies:                    0
% 20.18/3.03  qbf_prep_cycles:                        0
% 20.18/3.03  
% 20.18/3.03  ------ BMC1
% 20.18/3.03  
% 20.18/3.03  bmc1_current_bound:                     -1
% 20.18/3.03  bmc1_last_solved_bound:                 -1
% 20.18/3.03  bmc1_unsat_core_size:                   -1
% 20.18/3.03  bmc1_unsat_core_parents_size:           -1
% 20.18/3.03  bmc1_merge_next_fun:                    0
% 20.18/3.03  bmc1_unsat_core_clauses_time:           0.
% 20.18/3.03  
% 20.18/3.03  ------ Instantiation
% 20.18/3.03  
% 20.18/3.03  inst_num_of_clauses:                    355
% 20.18/3.03  inst_num_in_passive:                    76
% 20.18/3.03  inst_num_in_active:                     2841
% 20.18/3.03  inst_num_in_unprocessed:                103
% 20.18/3.03  inst_num_of_loops:                      3183
% 20.18/3.03  inst_num_of_learning_restarts:          1
% 20.18/3.03  inst_num_moves_active_passive:          335
% 20.18/3.03  inst_lit_activity:                      0
% 20.18/3.03  inst_lit_activity_moves:                0
% 20.18/3.03  inst_num_tautologies:                   0
% 20.18/3.03  inst_num_prop_implied:                  0
% 20.18/3.03  inst_num_existing_simplified:           0
% 20.18/3.03  inst_num_eq_res_simplified:             0
% 20.18/3.03  inst_num_child_elim:                    0
% 20.18/3.03  inst_num_of_dismatching_blockings:      9486
% 20.18/3.03  inst_num_of_non_proper_insts:           11213
% 20.18/3.03  inst_num_of_duplicates:                 0
% 20.18/3.03  inst_inst_num_from_inst_to_res:         0
% 20.18/3.03  inst_dismatching_checking_time:         0.
% 20.18/3.03  
% 20.18/3.03  ------ Resolution
% 20.18/3.03  
% 20.18/3.03  res_num_of_clauses:                     61
% 20.18/3.03  res_num_in_passive:                     61
% 20.18/3.03  res_num_in_active:                      0
% 20.18/3.03  res_num_of_loops:                       214
% 20.18/3.03  res_forward_subset_subsumed:            455
% 20.18/3.03  res_backward_subset_subsumed:           6
% 20.18/3.03  res_forward_subsumed:                   0
% 20.18/3.03  res_backward_subsumed:                  0
% 20.18/3.03  res_forward_subsumption_resolution:     0
% 20.18/3.03  res_backward_subsumption_resolution:    0
% 20.18/3.03  res_clause_to_clause_subsumption:       8643
% 20.18/3.03  res_orphan_elimination:                 0
% 20.18/3.03  res_tautology_del:                      615
% 20.18/3.03  res_num_eq_res_simplified:              0
% 20.18/3.03  res_num_sel_changes:                    0
% 20.18/3.03  res_moves_from_active_to_pass:          0
% 20.18/3.03  
% 20.18/3.03  ------ Superposition
% 20.18/3.03  
% 20.18/3.03  sup_time_total:                         0.
% 20.18/3.03  sup_time_generating:                    0.
% 20.18/3.03  sup_time_sim_full:                      0.
% 20.18/3.03  sup_time_sim_immed:                     0.
% 20.18/3.03  
% 20.18/3.03  sup_num_of_clauses:                     1917
% 20.18/3.03  sup_num_in_active:                      487
% 20.18/3.03  sup_num_in_passive:                     1430
% 20.18/3.03  sup_num_of_loops:                       636
% 20.18/3.03  sup_fw_superposition:                   1330
% 20.18/3.03  sup_bw_superposition:                   1839
% 20.18/3.03  sup_immediate_simplified:               1073
% 20.18/3.03  sup_given_eliminated:                   2
% 20.18/3.03  comparisons_done:                       0
% 20.18/3.03  comparisons_avoided:                    12
% 20.18/3.03  
% 20.18/3.03  ------ Simplifications
% 20.18/3.03  
% 20.18/3.03  
% 20.18/3.03  sim_fw_subset_subsumed:                 363
% 20.18/3.03  sim_bw_subset_subsumed:                 246
% 20.18/3.03  sim_fw_subsumed:                        247
% 20.18/3.03  sim_bw_subsumed:                        19
% 20.18/3.03  sim_fw_subsumption_res:                 6
% 20.18/3.03  sim_bw_subsumption_res:                 3
% 20.18/3.03  sim_tautology_del:                      58
% 20.18/3.03  sim_eq_tautology_del:                   55
% 20.18/3.03  sim_eq_res_simp:                        0
% 20.18/3.03  sim_fw_demodulated:                     4
% 20.18/3.03  sim_bw_demodulated:                     73
% 20.18/3.03  sim_light_normalised:                   633
% 20.18/3.03  sim_joinable_taut:                      0
% 20.18/3.03  sim_joinable_simp:                      0
% 20.18/3.03  sim_ac_normalised:                      0
% 20.18/3.03  sim_smt_subsumption:                    0
% 20.18/3.03  
%------------------------------------------------------------------------------
