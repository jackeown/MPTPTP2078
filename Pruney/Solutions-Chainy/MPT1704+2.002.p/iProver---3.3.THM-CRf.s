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
% DateTime   : Thu Dec  3 12:21:42 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  141 (1381 expanded)
%              Number of clauses        :   89 ( 299 expanded)
%              Number of leaves         :   17 ( 393 expanded)
%              Depth                    :   22
%              Number of atoms          :  621 (15932 expanded)
%              Number of equality atoms :  186 (1631 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_borsuk_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_borsuk_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_borsuk_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK2,X0)
          | ~ v1_borsuk_1(sK2,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
        & ( ( m1_pre_topc(sK2,X0)
            & v1_borsuk_1(sK2,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | ~ m1_pre_topc(sK1,X0)
              | ~ v1_borsuk_1(sK1,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
              | ( m1_pre_topc(sK1,X0)
                & v1_borsuk_1(sK1,X0) ) )
            & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_borsuk_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_borsuk_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_borsuk_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_borsuk_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_borsuk_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_borsuk_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_borsuk_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f53,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f54,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_723,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_728,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2253,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_728])).

cnf(c_2376,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_723,c_2253])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2483,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2376,c_25])).

cnf(c_10,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_726,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2353,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_726])).

cnf(c_2361,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2353,c_17])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_29,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2471,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2361,c_26,c_27,c_28,c_29])).

cnf(c_2489,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2483,c_2471])).

cnf(c_2370,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_2656,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2489,c_25,c_26,c_27,c_28,c_29,c_2370,c_2376])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_727,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2661,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_727])).

cnf(c_2665,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v1_pre_topc(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2661,c_17])).

cnf(c_320,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1860,plain,
    ( X0 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_320,c_17])).

cnf(c_324,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1959,plain,
    ( v1_pre_topc(X0)
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_1860,c_324])).

cnf(c_1662,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_319,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_344,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_943,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1022,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_325,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1154,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_325,c_17])).

cnf(c_330,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1165,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_330,c_17])).

cnf(c_328,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1056,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,sK0)
    | X1 != sK0
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1578,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | ~ m1_pre_topc(sK2,sK0)
    | X0 != sK0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1580,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_1665,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1662,c_22,c_21,c_20,c_19,c_18,c_17,c_344,c_943,c_1022,c_1154,c_1165,c_1580])).

cnf(c_2282,plain,
    ( v1_pre_topc(X0)
    | X0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1959,c_22,c_21,c_20,c_19,c_18,c_17,c_344,c_943,c_1022,c_1154,c_1165,c_1580,c_1662])).

cnf(c_2303,plain,
    ( v1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_2282,c_319])).

cnf(c_2304,plain,
    ( v1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_2777,plain,
    ( v1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2665,c_2304])).

cnf(c_719,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_732,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1425,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | v1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_732])).

cnf(c_2782,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2777,c_1425])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_729,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1792,plain,
    ( g1_pre_topc(X0,X1) != sK2
    | u1_struct_0(sK1) = X0
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_729])).

cnf(c_2789,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2782,c_1792])).

cnf(c_1,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2329,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2334,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2329])).

cnf(c_3144,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2789,c_27,c_2334])).

cnf(c_8,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_186,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_borsuk_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_11])).

cnf(c_187,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_712,plain,
    ( v1_borsuk_1(X0,X1) != iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_3154,plain,
    ( v1_borsuk_1(sK1,X0) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3144,c_712])).

cnf(c_3212,plain,
    ( v1_borsuk_1(sK1,sK0) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK0) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3154])).

cnf(c_7,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_177,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | v1_borsuk_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_11])).

cnf(c_178,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_713,plain,
    ( v1_borsuk_1(X0,X1) = iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_3151,plain,
    ( v1_borsuk_1(sK1,X0) = iProver_top
    | v4_pre_topc(u1_struct_0(sK2),X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3144,c_713])).

cnf(c_3206,plain,
    ( v1_borsuk_1(sK1,sK0) = iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3151])).

cnf(c_1120,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_1121,plain,
    ( v1_borsuk_1(sK2,sK0) = iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_1057,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_1067,plain,
    ( v1_borsuk_1(sK2,sK0) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_12,negated_conjecture,
    ( ~ v1_borsuk_1(sK1,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( v1_borsuk_1(sK1,sK0) != iProver_top
    | v1_borsuk_1(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,negated_conjecture,
    ( v1_borsuk_1(sK1,sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,plain,
    ( v1_borsuk_1(sK1,sK0) = iProver_top
    | v1_borsuk_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3212,c_3206,c_2376,c_2370,c_1121,c_1067,c_34,c_30,c_29,c_28,c_27,c_26,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.00  
% 3.37/1.00  ------  iProver source info
% 3.37/1.00  
% 3.37/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.00  git: non_committed_changes: false
% 3.37/1.00  git: last_make_outside_of_git: false
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  ------ Parsing...
% 3.37/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  ------ Proving...
% 3.37/1.00  ------ Problem Properties 
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  clauses                                 22
% 3.37/1.00  conjectures                             12
% 3.37/1.00  EPR                                     11
% 3.37/1.00  Horn                                    18
% 3.37/1.00  unary                                   7
% 3.37/1.00  binary                                  5
% 3.37/1.00  lits                                    56
% 3.37/1.00  lits eq                                 6
% 3.37/1.00  fd_pure                                 0
% 3.37/1.00  fd_pseudo                               0
% 3.37/1.00  fd_cond                                 0
% 3.37/1.00  fd_pseudo_cond                          2
% 3.37/1.00  AC symbols                              0
% 3.37/1.00  
% 3.37/1.00  ------ Input Options Time Limit: Unbounded
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  Current options:
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS status Theorem for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  fof(f8,conjecture,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f9,negated_conjecture,(
% 3.37/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 3.37/1.00    inference(negated_conjecture,[],[f8])).
% 3.37/1.00  
% 3.37/1.00  fof(f20,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f9])).
% 3.37/1.00  
% 3.37/1.00  fof(f21,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f20])).
% 3.37/1.00  
% 3.37/1.00  fof(f25,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f21])).
% 3.37/1.00  
% 3.37/1.00  fof(f26,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f25])).
% 3.37/1.00  
% 3.37/1.00  fof(f29,plain,(
% 3.37/1.00    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,X0) | ~v1_borsuk_1(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(sK2,X0) & v1_borsuk_1(sK2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f28,plain,(
% 3.37/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(sK1,X0) | ~v1_borsuk_1(sK1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(sK1,X0) & v1_borsuk_1(sK1,X0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f27,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f30,plain,(
% 3.37/1.00    (((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f53,plain,(
% 3.37/1.00    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f49,plain,(
% 3.37/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f4,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f14,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f4])).
% 3.37/1.00  
% 3.37/1.00  fof(f36,plain,(
% 3.37/1.00    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f14])).
% 3.37/1.00  
% 3.37/1.00  fof(f44,plain,(
% 3.37/1.00    l1_pre_topc(sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f6,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f17,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f6])).
% 3.37/1.00  
% 3.37/1.00  fof(f18,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f17])).
% 3.37/1.00  
% 3.37/1.00  fof(f24,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f18])).
% 3.37/1.00  
% 3.37/1.00  fof(f40,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f24])).
% 3.37/1.00  
% 3.37/1.00  fof(f59,plain,(
% 3.37/1.00    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f40])).
% 3.37/1.00  
% 3.37/1.00  fof(f45,plain,(
% 3.37/1.00    v2_pre_topc(sK1)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f46,plain,(
% 3.37/1.00    l1_pre_topc(sK1)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f47,plain,(
% 3.37/1.00    v2_pre_topc(sK2)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f48,plain,(
% 3.37/1.00    l1_pre_topc(sK2)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f35,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f14])).
% 3.37/1.00  
% 3.37/1.00  fof(f1,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f10,plain,(
% 3.37/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f1])).
% 3.37/1.00  
% 3.37/1.00  fof(f11,plain,(
% 3.37/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f10])).
% 3.37/1.00  
% 3.37/1.00  fof(f31,plain,(
% 3.37/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f11])).
% 3.37/1.00  
% 3.37/1.00  fof(f3,axiom,(
% 3.37/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f13,plain,(
% 3.37/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.37/1.00    inference(ennf_transformation,[],[f3])).
% 3.37/1.00  
% 3.37/1.00  fof(f33,plain,(
% 3.37/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f13])).
% 3.37/1.00  
% 3.37/1.00  fof(f2,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f12,plain,(
% 3.37/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f2])).
% 3.37/1.00  
% 3.37/1.00  fof(f32,plain,(
% 3.37/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f12])).
% 3.37/1.00  
% 3.37/1.00  fof(f5,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f15,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f5])).
% 3.37/1.00  
% 3.37/1.00  fof(f16,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f15])).
% 3.37/1.00  
% 3.37/1.00  fof(f22,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f16])).
% 3.37/1.00  
% 3.37/1.00  fof(f23,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/1.00    inference(flattening,[],[f22])).
% 3.37/1.00  
% 3.37/1.00  fof(f37,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f23])).
% 3.37/1.00  
% 3.37/1.00  fof(f57,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f37])).
% 3.37/1.00  
% 3.37/1.00  fof(f7,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f19,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f7])).
% 3.37/1.00  
% 3.37/1.00  fof(f42,plain,(
% 3.37/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f19])).
% 3.37/1.00  
% 3.37/1.00  fof(f38,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f23])).
% 3.37/1.00  
% 3.37/1.00  fof(f56,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f38])).
% 3.37/1.00  
% 3.37/1.00  fof(f54,plain,(
% 3.37/1.00    ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f50,plain,(
% 3.37/1.00    v1_borsuk_1(sK2,sK0) | v1_borsuk_1(sK1,sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f43,plain,(
% 3.37/1.00    v2_pre_topc(sK0)),
% 3.37/1.00    inference(cnf_transformation,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  cnf(c_13,negated_conjecture,
% 3.37/1.00      ( m1_pre_topc(sK1,sK0) | m1_pre_topc(sK2,sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_723,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,sK0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_17,negated_conjecture,
% 3.37/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 3.37/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_728,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2253,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) = iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_17,c_728]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2376,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_723,c_2253]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_22,negated_conjecture,
% 3.37/1.00      ( l1_pre_topc(sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_25,plain,
% 3.37/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2483,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2376,c_25]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_10,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.37/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_726,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) = iProver_top
% 3.37/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 3.37/1.00      | v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2353,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,X0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_17,c_726]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2361,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,X0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_2353,c_17]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_21,negated_conjecture,
% 3.37/1.00      ( v2_pre_topc(sK1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_26,plain,
% 3.37/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_20,negated_conjecture,
% 3.37/1.00      ( l1_pre_topc(sK1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_27,plain,
% 3.37/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_19,negated_conjecture,
% 3.37/1.00      ( v2_pre_topc(sK2) ),
% 3.37/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_28,plain,
% 3.37/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_18,negated_conjecture,
% 3.37/1.00      ( l1_pre_topc(sK2) ),
% 3.37/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_29,plain,
% 3.37/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2471,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,X0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2361,c_26,c_27,c_28,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2489,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,sK0) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2483,c_2471]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2370,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,sK0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_2361]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2656,plain,
% 3.37/1.00      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2489,c_25,c_26,c_27,c_28,c_29,c_2370,c_2376]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.37/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_727,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top
% 3.37/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2661,plain,
% 3.37/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.37/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2656,c_727]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2665,plain,
% 3.37/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.37/1.00      | v1_pre_topc(sK2) = iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_2661,c_17]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_320,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1860,plain,
% 3.37/1.00      ( X0 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | X0 != sK2 ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_320,c_17]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_324,plain,
% 3.37/1.00      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 3.37/1.00      theory(equality) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1959,plain,
% 3.37/1.00      ( v1_pre_topc(X0)
% 3.37/1.00      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.37/1.00      | X0 != sK2 ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_1860,c_324]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1662,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK0)
% 3.37/1.00      | ~ l1_pre_topc(sK0)
% 3.37/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_5,c_13]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_319,plain,( X0 = X0 ),theory(equality) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_344,plain,
% 3.37/1.00      ( sK0 = sK0 ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_319]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_943,plain,
% 3.37/1.00      ( ~ m1_pre_topc(sK1,sK0)
% 3.37/1.00      | ~ l1_pre_topc(sK0)
% 3.37/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1022,plain,
% 3.37/1.00      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
% 3.37/1.00      | m1_pre_topc(sK1,sK0)
% 3.37/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.37/1.00      | ~ v2_pre_topc(sK1)
% 3.37/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.37/1.00      | ~ l1_pre_topc(sK1)
% 3.37/1.00      | ~ l1_pre_topc(sK0) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_325,plain,
% 3.37/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 3.37/1.00      theory(equality) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1154,plain,
% 3.37/1.00      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_325,c_17]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_330,plain,
% 3.37/1.00      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 3.37/1.00      theory(equality) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1165,plain,
% 3.37/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.37/1.00      | ~ v2_pre_topc(sK2) ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_330,c_17]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_328,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.37/1.00      theory(equality) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1056,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.37/1.00      | X1 != sK0
% 3.37/1.00      | X0 != sK2 ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_328]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1578,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.37/1.00      | X0 != sK0
% 3.37/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_1056]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1580,plain,
% 3.37/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.37/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 3.37/1.00      | sK0 != sK0 ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_1578]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1665,plain,
% 3.37/1.00      ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_1662,c_22,c_21,c_20,c_19,c_18,c_17,c_344,c_943,c_1022,
% 3.37/1.00                 c_1154,c_1165,c_1580]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2282,plain,
% 3.37/1.00      ( v1_pre_topc(X0) | X0 != sK2 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_1959,c_22,c_21,c_20,c_19,c_18,c_17,c_344,c_943,c_1022,
% 3.37/1.00                 c_1154,c_1165,c_1580,c_1662]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2303,plain,
% 3.37/1.00      ( v1_pre_topc(sK2) ),
% 3.37/1.00      inference(resolution,[status(thm)],[c_2282,c_319]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2304,plain,
% 3.37/1.00      ( v1_pre_topc(sK2) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2777,plain,
% 3.37/1.00      ( v1_pre_topc(sK2) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2665,c_2304]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_719,plain,
% 3.37/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_0,plain,
% 3.37/1.00      ( ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ v1_pre_topc(X0)
% 3.37/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_732,plain,
% 3.37/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top
% 3.37/1.00      | v1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1425,plain,
% 3.37/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
% 3.37/1.00      | v1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_719,c_732]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2782,plain,
% 3.37/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2 ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2777,c_1425]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.37/1.00      | X2 = X1
% 3.37/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_729,plain,
% 3.37/1.00      ( X0 = X1
% 3.37/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.37/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1792,plain,
% 3.37/1.00      ( g1_pre_topc(X0,X1) != sK2
% 3.37/1.00      | u1_struct_0(sK1) = X0
% 3.37/1.00      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_17,c_729]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2789,plain,
% 3.37/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.37/1.00      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2782,c_1792]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1,plain,
% 3.37/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.37/1.00      | ~ l1_pre_topc(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2329,plain,
% 3.37/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.37/1.00      | ~ l1_pre_topc(sK1) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2334,plain,
% 3.37/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2329]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3144,plain,
% 3.37/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2789,c_27,c_2334]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8,plain,
% 3.37/1.00      ( ~ v1_borsuk_1(X0,X1)
% 3.37/1.00      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.37/1.00      | ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_11,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_186,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.37/1.00      | ~ v1_borsuk_1(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_8,c_11]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_187,plain,
% 3.37/1.00      ( ~ v1_borsuk_1(X0,X1)
% 3.37/1.00      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.37/1.00      | ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_186]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_712,plain,
% 3.37/1.00      ( v1_borsuk_1(X0,X1) != iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
% 3.37/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | v2_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3154,plain,
% 3.37/1.00      ( v1_borsuk_1(sK1,X0) != iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(sK2),X0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 3.37/1.00      | v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_3144,c_712]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3212,plain,
% 3.37/1.00      ( v1_borsuk_1(sK1,sK0) != iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(sK2),sK0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_3154]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7,plain,
% 3.37/1.00      ( v1_borsuk_1(X0,X1)
% 3.37/1.00      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 3.37/1.00      | ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_177,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 3.37/1.00      | v1_borsuk_1(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_7,c_11]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_178,plain,
% 3.37/1.00      ( v1_borsuk_1(X0,X1)
% 3.37/1.00      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 3.37/1.00      | ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_177]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_713,plain,
% 3.37/1.00      ( v1_borsuk_1(X0,X1) = iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 3.37/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | v2_pre_topc(X1) != iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3151,plain,
% 3.37/1.00      ( v1_borsuk_1(sK1,X0) = iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(sK2),X0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,X0) != iProver_top
% 3.37/1.00      | v2_pre_topc(X0) != iProver_top
% 3.37/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_3144,c_713]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3206,plain,
% 3.37/1.00      ( v1_borsuk_1(sK1,sK0) = iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(sK2),sK0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_3151]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1120,plain,
% 3.37/1.00      ( v1_borsuk_1(sK2,sK0)
% 3.37/1.00      | ~ v4_pre_topc(u1_struct_0(sK2),sK0)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.37/1.00      | ~ v2_pre_topc(sK0)
% 3.37/1.00      | ~ l1_pre_topc(sK0) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_178]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1121,plain,
% 3.37/1.00      ( v1_borsuk_1(sK2,sK0) = iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(sK2),sK0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1057,plain,
% 3.37/1.00      ( ~ v1_borsuk_1(sK2,sK0)
% 3.37/1.00      | v4_pre_topc(u1_struct_0(sK2),sK0)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.37/1.00      | ~ v2_pre_topc(sK0)
% 3.37/1.00      | ~ l1_pre_topc(sK0) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_187]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1067,plain,
% 3.37/1.00      ( v1_borsuk_1(sK2,sK0) != iProver_top
% 3.37/1.00      | v4_pre_topc(u1_struct_0(sK2),sK0) = iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.37/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.37/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_12,negated_conjecture,
% 3.37/1.00      ( ~ v1_borsuk_1(sK1,sK0)
% 3.37/1.00      | ~ v1_borsuk_1(sK2,sK0)
% 3.37/1.00      | ~ m1_pre_topc(sK1,sK0)
% 3.37/1.00      | ~ m1_pre_topc(sK2,sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_34,plain,
% 3.37/1.00      ( v1_borsuk_1(sK1,sK0) != iProver_top
% 3.37/1.00      | v1_borsuk_1(sK2,sK0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.37/1.00      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_16,negated_conjecture,
% 3.37/1.00      ( v1_borsuk_1(sK1,sK0) | v1_borsuk_1(sK2,sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_30,plain,
% 3.37/1.00      ( v1_borsuk_1(sK1,sK0) = iProver_top
% 3.37/1.00      | v1_borsuk_1(sK2,sK0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_23,negated_conjecture,
% 3.37/1.00      ( v2_pre_topc(sK0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_24,plain,
% 3.37/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(contradiction,plain,
% 3.37/1.00      ( $false ),
% 3.37/1.00      inference(minisat,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_3212,c_3206,c_2376,c_2370,c_1121,c_1067,c_34,c_30,
% 3.37/1.00                 c_29,c_28,c_27,c_26,c_25,c_24]) ).
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  ------                               Statistics
% 3.37/1.00  
% 3.37/1.00  ------ Selected
% 3.37/1.00  
% 3.37/1.00  total_time:                             0.192
% 3.37/1.00  
%------------------------------------------------------------------------------
