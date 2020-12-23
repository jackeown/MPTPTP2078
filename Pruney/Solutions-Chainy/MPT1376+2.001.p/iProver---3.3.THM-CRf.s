%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:08 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  180 (2446 expanded)
%              Number of clauses        :  125 ( 732 expanded)
%              Number of leaves         :   11 ( 468 expanded)
%              Depth                    :   24
%              Number of atoms          :  680 (14593 expanded)
%              Number of equality atoms :  254 (1129 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
     => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
          | ~ v1_tops_2(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          | ~ v1_tops_2(sK2,X0) )
        & ( ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(sK2,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ v1_tops_2(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
                & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & v1_tops_2(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
            | ~ v1_tops_2(X1,sK1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
              & v1_tops_2(X1,sK1) ) ) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      | ~ v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | ~ v1_tops_2(sK2,sK1) )
    & ( ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
      | ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        & v1_tops_2(sK2,sK1) ) )
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1502,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1514,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1959,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1516])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1517,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3237,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1517])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1515,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1936,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1515])).

cnf(c_4768,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3237,c_1936])).

cnf(c_4769,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4768])).

cnf(c_4776,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(superposition,[status(thm)],[c_1502,c_4769])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1512,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4869,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_1512])).

cnf(c_5023,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4869])).

cnf(c_23,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_57,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_59,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_5575,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5023,c_23,c_59])).

cnf(c_12,plain,
    ( v1_tops_2(X0,X1)
    | r2_hidden(sK0(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1510,plain,
    ( v1_tops_2(X0,X1) = iProver_top
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5731,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5575,c_1510])).

cnf(c_1696,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1697,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_1699,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_7685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),X0) = iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5731,c_23,c_59,c_1699])).

cnf(c_7686,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7685])).

cnf(c_17,negated_conjecture,
    ( v1_tops_2(sK2,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1505,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ v1_tops_2(X0,X1)
    | v3_pre_topc(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1508,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | v3_pre_topc(X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1518,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1635,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | v3_pre_topc(X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1508,c_1518])).

cnf(c_3727,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(sK2,sK1) = iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1635])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_327,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_328,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_20])).

cnf(c_333,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_334,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1506,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2396,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1518])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_390,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_391,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_395,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_20])).

cnf(c_396,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_1498,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_2756,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2396,c_1498])).

cnf(c_18,negated_conjecture,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1814,plain,
    ( ~ v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1820,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_3496,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2756,c_23,c_25,c_27,c_59,c_1699,c_1820,c_2396])).

cnf(c_3505,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3496,c_1518])).

cnf(c_8,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_369,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_370,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v3_pre_topc(X0,sK1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_20])).

cnf(c_375,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_1499,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2755,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2396,c_1499])).

cnf(c_3242,plain,
    ( v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2755,c_23,c_25,c_27,c_59,c_1699,c_1820,c_2396])).

cnf(c_3252,plain,
    ( v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3242,c_1516])).

cnf(c_1757,plain,
    ( ~ v1_tops_2(sK2,sK1)
    | v3_pre_topc(X0,sK1)
    | ~ r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1758,plain,
    ( v1_tops_2(sK2,sK1) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_2397,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1518])).

cnf(c_2715,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2397,c_1499])).

cnf(c_19,negated_conjecture,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_tops_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_26,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2876,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2715,c_23,c_24,c_26,c_59,c_1699,c_1820,c_2397])).

cnf(c_3796,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3252,c_23,c_1758,c_2876,c_3242,c_3505])).

cnf(c_3797,plain,
    ( v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3796])).

cnf(c_3979,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3727,c_334,c_3505,c_3797])).

cnf(c_3980,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3979])).

cnf(c_13,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1509,plain,
    ( v1_tops_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2304,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1499])).

cnf(c_3650,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2304,c_23,c_59,c_1699])).

cnf(c_3651,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3650])).

cnf(c_5589,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5575,c_3651])).

cnf(c_11,plain,
    ( v1_tops_2(X0,X1)
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1511,plain,
    ( v1_tops_2(X0,X1) = iProver_top
    | v3_pre_topc(sK0(X1,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5730,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5575,c_1511])).

cnf(c_7558,plain,
    ( v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5589,c_23,c_59,c_1699,c_5730])).

cnf(c_7559,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7558])).

cnf(c_7567,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3980,c_7559])).

cnf(c_7697,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7686,c_7567])).

cnf(c_5603,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5575,c_1506])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_348,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_349,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_20])).

cnf(c_354,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_1500,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_2398,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_1518])).

cnf(c_2873,plain,
    ( v1_tops_2(X0,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
    | r2_hidden(X1,sK0(sK1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_2398])).

cnf(c_605,plain,
    ( v1_tops_2(X0,X1)
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_606,plain,
    ( v1_tops_2(X0,sK1)
    | ~ v3_pre_topc(sK0(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_607,plain,
    ( v1_tops_2(X0,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_4750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
    | v1_tops_2(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2873,c_607])).

cnf(c_4751,plain,
    ( v1_tops_2(X0,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4750])).

cnf(c_6056,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5603,c_4751])).

cnf(c_1723,plain,
    ( v1_tops_2(sK2,sK1)
    | ~ v3_pre_topc(sK0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1724,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1723])).

cnf(c_6055,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | r2_hidden(sK0(sK1,sK2),sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5603,c_1510])).

cnf(c_6407,plain,
    ( r2_hidden(sK0(sK1,sK2),sK2) = iProver_top
    | v1_tops_2(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6055,c_23])).

cnf(c_6408,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | r2_hidden(sK0(sK1,sK2),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6407])).

cnf(c_6414,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6408,c_3797])).

cnf(c_6563,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6056,c_23,c_1724,c_5603,c_6414])).

cnf(c_15,negated_conjecture,
    ( ~ v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1507,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(sK2,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5605,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(sK2,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5575,c_1507])).

cnf(c_5618,plain,
    ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(sK2,sK1) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5603,c_5605])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7697,c_6563,c_5618,c_5603])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.24/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.00  
% 3.24/1.00  ------  iProver source info
% 3.24/1.00  
% 3.24/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.00  git: non_committed_changes: false
% 3.24/1.00  git: last_make_outside_of_git: false
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options
% 3.24/1.00  
% 3.24/1.00  --out_options                           all
% 3.24/1.00  --tptp_safe_out                         true
% 3.24/1.00  --problem_path                          ""
% 3.24/1.00  --include_path                          ""
% 3.24/1.00  --clausifier                            res/vclausify_rel
% 3.24/1.00  --clausifier_options                    --mode clausify
% 3.24/1.00  --stdin                                 false
% 3.24/1.00  --stats_out                             all
% 3.24/1.00  
% 3.24/1.00  ------ General Options
% 3.24/1.00  
% 3.24/1.00  --fof                                   false
% 3.24/1.00  --time_out_real                         305.
% 3.24/1.00  --time_out_virtual                      -1.
% 3.24/1.00  --symbol_type_check                     false
% 3.24/1.00  --clausify_out                          false
% 3.24/1.00  --sig_cnt_out                           false
% 3.24/1.00  --trig_cnt_out                          false
% 3.24/1.00  --trig_cnt_out_tolerance                1.
% 3.24/1.00  --trig_cnt_out_sk_spl                   false
% 3.24/1.00  --abstr_cl_out                          false
% 3.24/1.00  
% 3.24/1.00  ------ Global Options
% 3.24/1.00  
% 3.24/1.00  --schedule                              default
% 3.24/1.00  --add_important_lit                     false
% 3.24/1.00  --prop_solver_per_cl                    1000
% 3.24/1.00  --min_unsat_core                        false
% 3.24/1.00  --soft_assumptions                      false
% 3.24/1.00  --soft_lemma_size                       3
% 3.24/1.00  --prop_impl_unit_size                   0
% 3.24/1.00  --prop_impl_unit                        []
% 3.24/1.00  --share_sel_clauses                     true
% 3.24/1.00  --reset_solvers                         false
% 3.24/1.00  --bc_imp_inh                            [conj_cone]
% 3.24/1.00  --conj_cone_tolerance                   3.
% 3.24/1.00  --extra_neg_conj                        none
% 3.24/1.00  --large_theory_mode                     true
% 3.24/1.00  --prolific_symb_bound                   200
% 3.24/1.00  --lt_threshold                          2000
% 3.24/1.00  --clause_weak_htbl                      true
% 3.24/1.00  --gc_record_bc_elim                     false
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing Options
% 3.24/1.00  
% 3.24/1.00  --preprocessing_flag                    true
% 3.24/1.00  --time_out_prep_mult                    0.1
% 3.24/1.00  --splitting_mode                        input
% 3.24/1.00  --splitting_grd                         true
% 3.24/1.00  --splitting_cvd                         false
% 3.24/1.00  --splitting_cvd_svl                     false
% 3.24/1.00  --splitting_nvd                         32
% 3.24/1.00  --sub_typing                            true
% 3.24/1.00  --prep_gs_sim                           true
% 3.24/1.00  --prep_unflatten                        true
% 3.24/1.00  --prep_res_sim                          true
% 3.24/1.00  --prep_upred                            true
% 3.24/1.00  --prep_sem_filter                       exhaustive
% 3.24/1.00  --prep_sem_filter_out                   false
% 3.24/1.00  --pred_elim                             true
% 3.24/1.00  --res_sim_input                         true
% 3.24/1.00  --eq_ax_congr_red                       true
% 3.24/1.00  --pure_diseq_elim                       true
% 3.24/1.00  --brand_transform                       false
% 3.24/1.00  --non_eq_to_eq                          false
% 3.24/1.00  --prep_def_merge                        true
% 3.24/1.00  --prep_def_merge_prop_impl              false
% 3.24/1.00  --prep_def_merge_mbd                    true
% 3.24/1.00  --prep_def_merge_tr_red                 false
% 3.24/1.00  --prep_def_merge_tr_cl                  false
% 3.24/1.00  --smt_preprocessing                     true
% 3.24/1.00  --smt_ac_axioms                         fast
% 3.24/1.00  --preprocessed_out                      false
% 3.24/1.00  --preprocessed_stats                    false
% 3.24/1.00  
% 3.24/1.00  ------ Abstraction refinement Options
% 3.24/1.00  
% 3.24/1.00  --abstr_ref                             []
% 3.24/1.00  --abstr_ref_prep                        false
% 3.24/1.00  --abstr_ref_until_sat                   false
% 3.24/1.00  --abstr_ref_sig_restrict                funpre
% 3.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.00  --abstr_ref_under                       []
% 3.24/1.00  
% 3.24/1.00  ------ SAT Options
% 3.24/1.00  
% 3.24/1.00  --sat_mode                              false
% 3.24/1.00  --sat_fm_restart_options                ""
% 3.24/1.00  --sat_gr_def                            false
% 3.24/1.00  --sat_epr_types                         true
% 3.24/1.00  --sat_non_cyclic_types                  false
% 3.24/1.00  --sat_finite_models                     false
% 3.24/1.00  --sat_fm_lemmas                         false
% 3.24/1.00  --sat_fm_prep                           false
% 3.24/1.00  --sat_fm_uc_incr                        true
% 3.24/1.00  --sat_out_model                         small
% 3.24/1.00  --sat_out_clauses                       false
% 3.24/1.00  
% 3.24/1.00  ------ QBF Options
% 3.24/1.00  
% 3.24/1.00  --qbf_mode                              false
% 3.24/1.00  --qbf_elim_univ                         false
% 3.24/1.00  --qbf_dom_inst                          none
% 3.24/1.00  --qbf_dom_pre_inst                      false
% 3.24/1.00  --qbf_sk_in                             false
% 3.24/1.00  --qbf_pred_elim                         true
% 3.24/1.00  --qbf_split                             512
% 3.24/1.00  
% 3.24/1.00  ------ BMC1 Options
% 3.24/1.00  
% 3.24/1.00  --bmc1_incremental                      false
% 3.24/1.00  --bmc1_axioms                           reachable_all
% 3.24/1.00  --bmc1_min_bound                        0
% 3.24/1.00  --bmc1_max_bound                        -1
% 3.24/1.00  --bmc1_max_bound_default                -1
% 3.24/1.00  --bmc1_symbol_reachability              true
% 3.24/1.00  --bmc1_property_lemmas                  false
% 3.24/1.00  --bmc1_k_induction                      false
% 3.24/1.00  --bmc1_non_equiv_states                 false
% 3.24/1.00  --bmc1_deadlock                         false
% 3.24/1.00  --bmc1_ucm                              false
% 3.24/1.00  --bmc1_add_unsat_core                   none
% 3.24/1.00  --bmc1_unsat_core_children              false
% 3.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.00  --bmc1_out_stat                         full
% 3.24/1.00  --bmc1_ground_init                      false
% 3.24/1.00  --bmc1_pre_inst_next_state              false
% 3.24/1.00  --bmc1_pre_inst_state                   false
% 3.24/1.00  --bmc1_pre_inst_reach_state             false
% 3.24/1.00  --bmc1_out_unsat_core                   false
% 3.24/1.00  --bmc1_aig_witness_out                  false
% 3.24/1.00  --bmc1_verbose                          false
% 3.24/1.00  --bmc1_dump_clauses_tptp                false
% 3.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.00  --bmc1_dump_file                        -
% 3.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.00  --bmc1_ucm_extend_mode                  1
% 3.24/1.00  --bmc1_ucm_init_mode                    2
% 3.24/1.00  --bmc1_ucm_cone_mode                    none
% 3.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.00  --bmc1_ucm_relax_model                  4
% 3.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.00  --bmc1_ucm_layered_model                none
% 3.24/1.00  --bmc1_ucm_max_lemma_size               10
% 3.24/1.00  
% 3.24/1.00  ------ AIG Options
% 3.24/1.00  
% 3.24/1.00  --aig_mode                              false
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation Options
% 3.24/1.00  
% 3.24/1.00  --instantiation_flag                    true
% 3.24/1.00  --inst_sos_flag                         false
% 3.24/1.00  --inst_sos_phase                        true
% 3.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel_side                     num_symb
% 3.24/1.00  --inst_solver_per_active                1400
% 3.24/1.00  --inst_solver_calls_frac                1.
% 3.24/1.00  --inst_passive_queue_type               priority_queues
% 3.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.00  --inst_passive_queues_freq              [25;2]
% 3.24/1.00  --inst_dismatching                      true
% 3.24/1.00  --inst_eager_unprocessed_to_passive     true
% 3.24/1.00  --inst_prop_sim_given                   true
% 3.24/1.00  --inst_prop_sim_new                     false
% 3.24/1.00  --inst_subs_new                         false
% 3.24/1.00  --inst_eq_res_simp                      false
% 3.24/1.00  --inst_subs_given                       false
% 3.24/1.00  --inst_orphan_elimination               true
% 3.24/1.00  --inst_learning_loop_flag               true
% 3.24/1.00  --inst_learning_start                   3000
% 3.24/1.00  --inst_learning_factor                  2
% 3.24/1.00  --inst_start_prop_sim_after_learn       3
% 3.24/1.00  --inst_sel_renew                        solver
% 3.24/1.00  --inst_lit_activity_flag                true
% 3.24/1.00  --inst_restr_to_given                   false
% 3.24/1.00  --inst_activity_threshold               500
% 3.24/1.00  --inst_out_proof                        true
% 3.24/1.00  
% 3.24/1.00  ------ Resolution Options
% 3.24/1.00  
% 3.24/1.00  --resolution_flag                       true
% 3.24/1.00  --res_lit_sel                           adaptive
% 3.24/1.00  --res_lit_sel_side                      none
% 3.24/1.00  --res_ordering                          kbo
% 3.24/1.00  --res_to_prop_solver                    active
% 3.24/1.00  --res_prop_simpl_new                    false
% 3.24/1.00  --res_prop_simpl_given                  true
% 3.24/1.00  --res_passive_queue_type                priority_queues
% 3.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.00  --res_passive_queues_freq               [15;5]
% 3.24/1.00  --res_forward_subs                      full
% 3.24/1.00  --res_backward_subs                     full
% 3.24/1.00  --res_forward_subs_resolution           true
% 3.24/1.00  --res_backward_subs_resolution          true
% 3.24/1.00  --res_orphan_elimination                true
% 3.24/1.00  --res_time_limit                        2.
% 3.24/1.00  --res_out_proof                         true
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Options
% 3.24/1.00  
% 3.24/1.00  --superposition_flag                    true
% 3.24/1.00  --sup_passive_queue_type                priority_queues
% 3.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.00  --demod_completeness_check              fast
% 3.24/1.00  --demod_use_ground                      true
% 3.24/1.00  --sup_to_prop_solver                    passive
% 3.24/1.00  --sup_prop_simpl_new                    true
% 3.24/1.00  --sup_prop_simpl_given                  true
% 3.24/1.00  --sup_fun_splitting                     false
% 3.24/1.00  --sup_smt_interval                      50000
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Simplification Setup
% 3.24/1.00  
% 3.24/1.00  --sup_indices_passive                   []
% 3.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_full_bw                           [BwDemod]
% 3.24/1.00  --sup_immed_triv                        [TrivRules]
% 3.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_immed_bw_main                     []
% 3.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  
% 3.24/1.00  ------ Combination Options
% 3.24/1.00  
% 3.24/1.00  --comb_res_mult                         3
% 3.24/1.00  --comb_sup_mult                         2
% 3.24/1.00  --comb_inst_mult                        10
% 3.24/1.00  
% 3.24/1.00  ------ Debug Options
% 3.24/1.00  
% 3.24/1.00  --dbg_backtrace                         false
% 3.24/1.00  --dbg_dump_prop_clauses                 false
% 3.24/1.00  --dbg_dump_prop_clauses_file            -
% 3.24/1.00  --dbg_out_stat                          false
% 3.24/1.00  ------ Parsing...
% 3.24/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.00  ------ Proving...
% 3.24/1.00  ------ Problem Properties 
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  clauses                                 21
% 3.24/1.00  conjectures                             6
% 3.24/1.00  EPR                                     1
% 3.24/1.00  Horn                                    15
% 3.24/1.00  unary                                   1
% 3.24/1.00  binary                                  7
% 3.24/1.00  lits                                    61
% 3.24/1.00  lits eq                                 5
% 3.24/1.00  fd_pure                                 0
% 3.24/1.00  fd_pseudo                               0
% 3.24/1.00  fd_cond                                 0
% 3.24/1.00  fd_pseudo_cond                          2
% 3.24/1.00  AC symbols                              0
% 3.24/1.00  
% 3.24/1.00  ------ Schedule dynamic 5 is on 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  Current options:
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options
% 3.24/1.00  
% 3.24/1.00  --out_options                           all
% 3.24/1.00  --tptp_safe_out                         true
% 3.24/1.00  --problem_path                          ""
% 3.24/1.00  --include_path                          ""
% 3.24/1.00  --clausifier                            res/vclausify_rel
% 3.24/1.00  --clausifier_options                    --mode clausify
% 3.24/1.00  --stdin                                 false
% 3.24/1.00  --stats_out                             all
% 3.24/1.00  
% 3.24/1.00  ------ General Options
% 3.24/1.00  
% 3.24/1.00  --fof                                   false
% 3.24/1.00  --time_out_real                         305.
% 3.24/1.00  --time_out_virtual                      -1.
% 3.24/1.00  --symbol_type_check                     false
% 3.24/1.00  --clausify_out                          false
% 3.24/1.00  --sig_cnt_out                           false
% 3.24/1.00  --trig_cnt_out                          false
% 3.24/1.00  --trig_cnt_out_tolerance                1.
% 3.24/1.00  --trig_cnt_out_sk_spl                   false
% 3.24/1.00  --abstr_cl_out                          false
% 3.24/1.00  
% 3.24/1.00  ------ Global Options
% 3.24/1.00  
% 3.24/1.00  --schedule                              default
% 3.24/1.00  --add_important_lit                     false
% 3.24/1.00  --prop_solver_per_cl                    1000
% 3.24/1.00  --min_unsat_core                        false
% 3.24/1.00  --soft_assumptions                      false
% 3.24/1.00  --soft_lemma_size                       3
% 3.24/1.00  --prop_impl_unit_size                   0
% 3.24/1.00  --prop_impl_unit                        []
% 3.24/1.00  --share_sel_clauses                     true
% 3.24/1.00  --reset_solvers                         false
% 3.24/1.00  --bc_imp_inh                            [conj_cone]
% 3.24/1.00  --conj_cone_tolerance                   3.
% 3.24/1.00  --extra_neg_conj                        none
% 3.24/1.00  --large_theory_mode                     true
% 3.24/1.00  --prolific_symb_bound                   200
% 3.24/1.00  --lt_threshold                          2000
% 3.24/1.00  --clause_weak_htbl                      true
% 3.24/1.00  --gc_record_bc_elim                     false
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing Options
% 3.24/1.00  
% 3.24/1.00  --preprocessing_flag                    true
% 3.24/1.00  --time_out_prep_mult                    0.1
% 3.24/1.00  --splitting_mode                        input
% 3.24/1.00  --splitting_grd                         true
% 3.24/1.00  --splitting_cvd                         false
% 3.24/1.00  --splitting_cvd_svl                     false
% 3.24/1.00  --splitting_nvd                         32
% 3.24/1.00  --sub_typing                            true
% 3.24/1.00  --prep_gs_sim                           true
% 3.24/1.00  --prep_unflatten                        true
% 3.24/1.00  --prep_res_sim                          true
% 3.24/1.00  --prep_upred                            true
% 3.24/1.00  --prep_sem_filter                       exhaustive
% 3.24/1.00  --prep_sem_filter_out                   false
% 3.24/1.00  --pred_elim                             true
% 3.24/1.00  --res_sim_input                         true
% 3.24/1.00  --eq_ax_congr_red                       true
% 3.24/1.00  --pure_diseq_elim                       true
% 3.24/1.00  --brand_transform                       false
% 3.24/1.00  --non_eq_to_eq                          false
% 3.24/1.00  --prep_def_merge                        true
% 3.24/1.00  --prep_def_merge_prop_impl              false
% 3.24/1.00  --prep_def_merge_mbd                    true
% 3.24/1.00  --prep_def_merge_tr_red                 false
% 3.24/1.00  --prep_def_merge_tr_cl                  false
% 3.24/1.00  --smt_preprocessing                     true
% 3.24/1.00  --smt_ac_axioms                         fast
% 3.24/1.00  --preprocessed_out                      false
% 3.24/1.00  --preprocessed_stats                    false
% 3.24/1.00  
% 3.24/1.00  ------ Abstraction refinement Options
% 3.24/1.00  
% 3.24/1.00  --abstr_ref                             []
% 3.24/1.00  --abstr_ref_prep                        false
% 3.24/1.00  --abstr_ref_until_sat                   false
% 3.24/1.00  --abstr_ref_sig_restrict                funpre
% 3.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.00  --abstr_ref_under                       []
% 3.24/1.00  
% 3.24/1.00  ------ SAT Options
% 3.24/1.00  
% 3.24/1.00  --sat_mode                              false
% 3.24/1.00  --sat_fm_restart_options                ""
% 3.24/1.00  --sat_gr_def                            false
% 3.24/1.00  --sat_epr_types                         true
% 3.24/1.00  --sat_non_cyclic_types                  false
% 3.24/1.00  --sat_finite_models                     false
% 3.24/1.00  --sat_fm_lemmas                         false
% 3.24/1.00  --sat_fm_prep                           false
% 3.24/1.00  --sat_fm_uc_incr                        true
% 3.24/1.00  --sat_out_model                         small
% 3.24/1.00  --sat_out_clauses                       false
% 3.24/1.00  
% 3.24/1.00  ------ QBF Options
% 3.24/1.00  
% 3.24/1.00  --qbf_mode                              false
% 3.24/1.00  --qbf_elim_univ                         false
% 3.24/1.00  --qbf_dom_inst                          none
% 3.24/1.00  --qbf_dom_pre_inst                      false
% 3.24/1.00  --qbf_sk_in                             false
% 3.24/1.00  --qbf_pred_elim                         true
% 3.24/1.00  --qbf_split                             512
% 3.24/1.00  
% 3.24/1.00  ------ BMC1 Options
% 3.24/1.00  
% 3.24/1.00  --bmc1_incremental                      false
% 3.24/1.00  --bmc1_axioms                           reachable_all
% 3.24/1.00  --bmc1_min_bound                        0
% 3.24/1.00  --bmc1_max_bound                        -1
% 3.24/1.00  --bmc1_max_bound_default                -1
% 3.24/1.00  --bmc1_symbol_reachability              true
% 3.24/1.00  --bmc1_property_lemmas                  false
% 3.24/1.00  --bmc1_k_induction                      false
% 3.24/1.00  --bmc1_non_equiv_states                 false
% 3.24/1.00  --bmc1_deadlock                         false
% 3.24/1.00  --bmc1_ucm                              false
% 3.24/1.00  --bmc1_add_unsat_core                   none
% 3.24/1.00  --bmc1_unsat_core_children              false
% 3.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.00  --bmc1_out_stat                         full
% 3.24/1.00  --bmc1_ground_init                      false
% 3.24/1.00  --bmc1_pre_inst_next_state              false
% 3.24/1.00  --bmc1_pre_inst_state                   false
% 3.24/1.00  --bmc1_pre_inst_reach_state             false
% 3.24/1.00  --bmc1_out_unsat_core                   false
% 3.24/1.00  --bmc1_aig_witness_out                  false
% 3.24/1.00  --bmc1_verbose                          false
% 3.24/1.00  --bmc1_dump_clauses_tptp                false
% 3.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.00  --bmc1_dump_file                        -
% 3.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.00  --bmc1_ucm_extend_mode                  1
% 3.24/1.00  --bmc1_ucm_init_mode                    2
% 3.24/1.00  --bmc1_ucm_cone_mode                    none
% 3.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.00  --bmc1_ucm_relax_model                  4
% 3.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.00  --bmc1_ucm_layered_model                none
% 3.24/1.00  --bmc1_ucm_max_lemma_size               10
% 3.24/1.00  
% 3.24/1.00  ------ AIG Options
% 3.24/1.00  
% 3.24/1.00  --aig_mode                              false
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation Options
% 3.24/1.00  
% 3.24/1.00  --instantiation_flag                    true
% 3.24/1.00  --inst_sos_flag                         false
% 3.24/1.00  --inst_sos_phase                        true
% 3.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel_side                     none
% 3.24/1.00  --inst_solver_per_active                1400
% 3.24/1.00  --inst_solver_calls_frac                1.
% 3.24/1.00  --inst_passive_queue_type               priority_queues
% 3.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.00  --inst_passive_queues_freq              [25;2]
% 3.24/1.00  --inst_dismatching                      true
% 3.24/1.00  --inst_eager_unprocessed_to_passive     true
% 3.24/1.00  --inst_prop_sim_given                   true
% 3.24/1.00  --inst_prop_sim_new                     false
% 3.24/1.00  --inst_subs_new                         false
% 3.24/1.00  --inst_eq_res_simp                      false
% 3.24/1.00  --inst_subs_given                       false
% 3.24/1.00  --inst_orphan_elimination               true
% 3.24/1.00  --inst_learning_loop_flag               true
% 3.24/1.00  --inst_learning_start                   3000
% 3.24/1.00  --inst_learning_factor                  2
% 3.24/1.00  --inst_start_prop_sim_after_learn       3
% 3.24/1.00  --inst_sel_renew                        solver
% 3.24/1.00  --inst_lit_activity_flag                true
% 3.24/1.00  --inst_restr_to_given                   false
% 3.24/1.00  --inst_activity_threshold               500
% 3.24/1.00  --inst_out_proof                        true
% 3.24/1.00  
% 3.24/1.00  ------ Resolution Options
% 3.24/1.00  
% 3.24/1.00  --resolution_flag                       false
% 3.24/1.00  --res_lit_sel                           adaptive
% 3.24/1.00  --res_lit_sel_side                      none
% 3.24/1.00  --res_ordering                          kbo
% 3.24/1.00  --res_to_prop_solver                    active
% 3.24/1.00  --res_prop_simpl_new                    false
% 3.24/1.00  --res_prop_simpl_given                  true
% 3.24/1.00  --res_passive_queue_type                priority_queues
% 3.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.00  --res_passive_queues_freq               [15;5]
% 3.24/1.00  --res_forward_subs                      full
% 3.24/1.00  --res_backward_subs                     full
% 3.24/1.00  --res_forward_subs_resolution           true
% 3.24/1.00  --res_backward_subs_resolution          true
% 3.24/1.00  --res_orphan_elimination                true
% 3.24/1.00  --res_time_limit                        2.
% 3.24/1.00  --res_out_proof                         true
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Options
% 3.24/1.00  
% 3.24/1.00  --superposition_flag                    true
% 3.24/1.00  --sup_passive_queue_type                priority_queues
% 3.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.00  --demod_completeness_check              fast
% 3.24/1.00  --demod_use_ground                      true
% 3.24/1.00  --sup_to_prop_solver                    passive
% 3.24/1.00  --sup_prop_simpl_new                    true
% 3.24/1.00  --sup_prop_simpl_given                  true
% 3.24/1.00  --sup_fun_splitting                     false
% 3.24/1.00  --sup_smt_interval                      50000
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Simplification Setup
% 3.24/1.00  
% 3.24/1.00  --sup_indices_passive                   []
% 3.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_full_bw                           [BwDemod]
% 3.24/1.00  --sup_immed_triv                        [TrivRules]
% 3.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_immed_bw_main                     []
% 3.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  
% 3.24/1.00  ------ Combination Options
% 3.24/1.00  
% 3.24/1.00  --comb_res_mult                         3
% 3.24/1.00  --comb_sup_mult                         2
% 3.24/1.00  --comb_inst_mult                        10
% 3.24/1.00  
% 3.24/1.00  ------ Debug Options
% 3.24/1.00  
% 3.24/1.00  --dbg_backtrace                         false
% 3.24/1.00  --dbg_dump_prop_clauses                 false
% 3.24/1.00  --dbg_dump_prop_clauses_file            -
% 3.24/1.00  --dbg_out_stat                          false
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ Proving...
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS status Theorem for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  fof(f8,conjecture,(
% 3.24/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f9,negated_conjecture,(
% 3.24/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.24/1.00    inference(negated_conjecture,[],[f8])).
% 3.24/1.00  
% 3.24/1.00  fof(f10,plain,(
% 3.24/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.24/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.24/1.00  
% 3.24/1.00  fof(f22,plain,(
% 3.24/1.00    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.24/1.00    inference(ennf_transformation,[],[f10])).
% 3.24/1.00  
% 3.24/1.00  fof(f23,plain,(
% 3.24/1.00    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.24/1.00    inference(flattening,[],[f22])).
% 3.24/1.00  
% 3.24/1.00  fof(f30,plain,(
% 3.24/1.00    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.24/1.00    inference(nnf_transformation,[],[f23])).
% 3.24/1.00  
% 3.24/1.00  fof(f31,plain,(
% 3.24/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.24/1.00    inference(flattening,[],[f30])).
% 3.24/1.00  
% 3.24/1.00  fof(f33,plain,(
% 3.24/1.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK2,X0)) & ((m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(sK2,X0))))) )),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f32,plain,(
% 3.24/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~v1_tops_2(X1,sK1)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_2(X1,sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f34,plain,(
% 3.24/1.00    ((~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~v1_tops_2(sK2,sK1)) & ((m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_2(sK2,sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).
% 3.24/1.00  
% 3.24/1.00  fof(f51,plain,(
% 3.24/1.00    l1_pre_topc(sK1)),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f4,axiom,(
% 3.24/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f16,plain,(
% 3.24/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(ennf_transformation,[],[f4])).
% 3.24/1.00  
% 3.24/1.00  fof(f39,plain,(
% 3.24/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f16])).
% 3.24/1.00  
% 3.24/1.00  fof(f3,axiom,(
% 3.24/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f15,plain,(
% 3.24/1.00    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.24/1.00    inference(ennf_transformation,[],[f3])).
% 3.24/1.00  
% 3.24/1.00  fof(f38,plain,(
% 3.24/1.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f15])).
% 3.24/1.00  
% 3.24/1.00  fof(f2,axiom,(
% 3.24/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f13,plain,(
% 3.24/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(ennf_transformation,[],[f2])).
% 3.24/1.00  
% 3.24/1.00  fof(f14,plain,(
% 3.24/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(flattening,[],[f13])).
% 3.24/1.00  
% 3.24/1.00  fof(f36,plain,(
% 3.24/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f14])).
% 3.24/1.00  
% 3.24/1.00  fof(f37,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f15])).
% 3.24/1.00  
% 3.24/1.00  fof(f5,axiom,(
% 3.24/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f17,plain,(
% 3.24/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.24/1.00    inference(ennf_transformation,[],[f5])).
% 3.24/1.00  
% 3.24/1.00  fof(f40,plain,(
% 3.24/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f17])).
% 3.24/1.00  
% 3.24/1.00  fof(f7,axiom,(
% 3.24/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f20,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(ennf_transformation,[],[f7])).
% 3.24/1.00  
% 3.24/1.00  fof(f21,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(flattening,[],[f20])).
% 3.24/1.00  
% 3.24/1.00  fof(f26,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(nnf_transformation,[],[f21])).
% 3.24/1.00  
% 3.24/1.00  fof(f27,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(rectify,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f28,plain,(
% 3.24/1.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f29,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.24/1.00  
% 3.24/1.00  fof(f48,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f29])).
% 3.24/1.00  
% 3.24/1.00  fof(f54,plain,(
% 3.24/1.00    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v1_tops_2(sK2,sK1)),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f46,plain,(
% 3.24/1.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f29])).
% 3.24/1.00  
% 3.24/1.00  fof(f1,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f11,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.24/1.00    inference(ennf_transformation,[],[f1])).
% 3.24/1.00  
% 3.24/1.00  fof(f12,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.24/1.00    inference(flattening,[],[f11])).
% 3.24/1.00  
% 3.24/1.00  fof(f35,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f12])).
% 3.24/1.00  
% 3.24/1.00  fof(f6,axiom,(
% 3.24/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f18,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.24/1.00    inference(ennf_transformation,[],[f6])).
% 3.24/1.00  
% 3.24/1.00  fof(f19,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.24/1.00    inference(flattening,[],[f18])).
% 3.24/1.00  
% 3.24/1.00  fof(f24,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.24/1.00    inference(nnf_transformation,[],[f19])).
% 3.24/1.00  
% 3.24/1.00  fof(f25,plain,(
% 3.24/1.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.24/1.00    inference(flattening,[],[f24])).
% 3.24/1.00  
% 3.24/1.00  fof(f42,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f25])).
% 3.24/1.00  
% 3.24/1.00  fof(f50,plain,(
% 3.24/1.00    v2_pre_topc(sK1)),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f55,plain,(
% 3.24/1.00    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f45,plain,(
% 3.24/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f25])).
% 3.24/1.00  
% 3.24/1.00  fof(f53,plain,(
% 3.24/1.00    v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f44,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f25])).
% 3.24/1.00  
% 3.24/1.00  fof(f52,plain,(
% 3.24/1.00    v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_tops_2(sK2,sK1)),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f47,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f29])).
% 3.24/1.00  
% 3.24/1.00  fof(f49,plain,(
% 3.24/1.00    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f29])).
% 3.24/1.00  
% 3.24/1.00  fof(f43,plain,(
% 3.24/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f25])).
% 3.24/1.00  
% 3.24/1.00  fof(f56,plain,(
% 3.24/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~v1_tops_2(sK2,sK1)),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  cnf(c_20,negated_conjecture,
% 3.24/1.00      ( l1_pre_topc(sK1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1502,plain,
% 3.24/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4,plain,
% 3.24/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.24/1.00      | ~ l1_pre_topc(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1514,plain,
% 3.24/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.24/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.24/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1516,plain,
% 3.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1959,plain,
% 3.24/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1514,c_1516]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1,plain,
% 3.24/1.00      ( ~ l1_pre_topc(X0)
% 3.24/1.00      | ~ v1_pre_topc(X0)
% 3.24/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1517,plain,
% 3.24/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.24/1.00      | l1_pre_topc(X0) != iProver_top
% 3.24/1.00      | v1_pre_topc(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3237,plain,
% 3.24/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.24/1.00      | l1_pre_topc(X0) != iProver_top
% 3.24/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1959,c_1517]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.24/1.00      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.24/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1515,plain,
% 3.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.24/1.00      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1936,plain,
% 3.24/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.24/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1514,c_1515]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4768,plain,
% 3.24/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.24/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_3237,c_1936]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4769,plain,
% 3.24/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.24/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.24/1.00      inference(renaming,[status(thm)],[c_4768]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4776,plain,
% 3.24/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1502,c_4769]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.24/1.00      | X2 = X1
% 3.24/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1512,plain,
% 3.24/1.00      ( X0 = X1
% 3.24/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.24/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4869,plain,
% 3.24/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.24/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 3.24/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_4776,c_1512]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5023,plain,
% 3.24/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
% 3.24/1.00      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.00      inference(equality_resolution,[status(thm)],[c_4869]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_23,plain,
% 3.24/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_57,plain,
% 3.24/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.24/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_59,plain,
% 3.24/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.24/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_57]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5575,plain,
% 3.24/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_5023,c_23,c_59]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_12,plain,
% 3.24/1.00      ( v1_tops_2(X0,X1)
% 3.24/1.00      | r2_hidden(sK0(X1,X0),X0)
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.24/1.00      | ~ l1_pre_topc(X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1510,plain,
% 3.24/1.00      ( v1_tops_2(X0,X1) = iProver_top
% 3.24/1.00      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.24/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5731,plain,
% 3.24/1.00      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.00      | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),X0) = iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_5575,c_1510]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1696,plain,
% 3.24/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1697,plain,
% 3.24/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1699,plain,
% 3.24/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1697]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7685,plain,
% 3.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.00      | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),X0) = iProver_top
% 3.24/1.00      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_5731,c_23,c_59,c_1699]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7686,plain,
% 3.24/1.00      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.00      | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),X0) = iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.00      inference(renaming,[status(thm)],[c_7685]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_17,negated_conjecture,
% 3.24/1.00      ( v1_tops_2(sK2,sK1)
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1505,plain,
% 3.24/1.00      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_14,plain,
% 3.24/1.00      ( ~ v1_tops_2(X0,X1)
% 3.24/1.00      | v3_pre_topc(X2,X1)
% 3.24/1.00      | ~ r2_hidden(X2,X0)
% 3.24/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.24/1.00      | ~ l1_pre_topc(X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1508,plain,
% 3.24/1.00      ( v1_tops_2(X0,X1) != iProver_top
% 3.24/1.00      | v3_pre_topc(X2,X1) = iProver_top
% 3.24/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.24/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.24/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_0,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1)
% 3.24/1.00      | m1_subset_1(X0,X2)
% 3.24/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.24/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1518,plain,
% 3.24/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,X2) = iProver_top
% 3.24/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1635,plain,
% 3.24/1.00      ( v1_tops_2(X0,X1) != iProver_top
% 3.24/1.00      | v3_pre_topc(X2,X1) = iProver_top
% 3.24/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.24/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.24/1.00      inference(forward_subsumption_resolution,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_1508,c_1518]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3727,plain,
% 3.24/1.00      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.00      | v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1505,c_1635]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_10,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.00      | ~ v2_pre_topc(X1)
% 3.24/1.00      | ~ l1_pre_topc(X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_21,negated_conjecture,
% 3.24/1.00      ( v2_pre_topc(sK1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_327,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.00      | ~ l1_pre_topc(X1)
% 3.24/1.00      | sK1 != X1 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_328,plain,
% 3.24/1.00      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | ~ v3_pre_topc(X0,sK1)
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.24/1.00      | ~ l1_pre_topc(sK1) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_327]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_332,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.24/1.00      | ~ v3_pre_topc(X0,sK1)
% 3.24/1.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_328,c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_333,plain,
% 3.24/1.00      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | ~ v3_pre_topc(X0,sK1)
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.24/1.00      inference(renaming,[status(thm)],[c_332]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_334,plain,
% 3.24/1.00      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_16,negated_conjecture,
% 3.24/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1506,plain,
% 3.24/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2396,plain,
% 3.24/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1506,c_1518]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.24/1.00      | ~ v2_pre_topc(X1)
% 3.24/1.00      | ~ l1_pre_topc(X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_390,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.24/1.00      | ~ l1_pre_topc(X1)
% 3.24/1.00      | sK1 != X1 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_391,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.24/1.00      | ~ l1_pre_topc(sK1) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_395,plain,
% 3.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.00      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_391,c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_396,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.24/1.00      inference(renaming,[status(thm)],[c_395]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1498,plain,
% 3.24/1.00      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2756,plain,
% 3.24/1.00      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_2396,c_1498]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_18,negated_conjecture,
% 3.24/1.00      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_25,plain,
% 3.24/1.00      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_27,plain,
% 3.24/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1814,plain,
% 3.24/1.00      ( ~ v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | ~ r2_hidden(X0,sK2)
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.24/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1820,plain,
% 3.24/1.00      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.24/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3496,plain,
% 3.24/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.24/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_2756,c_23,c_25,c_27,c_59,c_1699,c_1820,c_2396]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3505,plain,
% 3.24/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.24/1.00      inference(forward_subsumption_resolution,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_3496,c_1518]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8,plain,
% 3.24/1.00      ( v3_pre_topc(X0,X1)
% 3.24/1.00      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.24/1.00      | ~ v2_pre_topc(X1)
% 3.24/1.00      | ~ l1_pre_topc(X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_369,plain,
% 3.24/1.00      ( v3_pre_topc(X0,X1)
% 3.24/1.00      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.24/1.00      | ~ l1_pre_topc(X1)
% 3.24/1.00      | sK1 != X1 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_370,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | v3_pre_topc(X0,sK1)
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.00      | ~ l1_pre_topc(sK1) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_369]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_374,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.00      | v3_pre_topc(X0,sK1)
% 3.24/1.00      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_370,c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_375,plain,
% 3.24/1.00      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.00      | v3_pre_topc(X0,sK1)
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
% 3.24/1.00      inference(renaming,[status(thm)],[c_374]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1499,plain,
% 3.24/1.00      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.00      | v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2755,plain,
% 3.24/1.01      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2396,c_1499]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3242,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_2755,c_23,c_25,c_27,c_59,c_1699,c_1820,c_2396]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3252,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK2)) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_3242,c_1516]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1757,plain,
% 3.24/1.01      ( ~ v1_tops_2(sK2,sK1)
% 3.24/1.01      | v3_pre_topc(X0,sK1)
% 3.24/1.01      | ~ r2_hidden(X0,sK2)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.24/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.24/1.01      | ~ l1_pre_topc(sK1) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1758,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) != iProver_top
% 3.24/1.01      | v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2397,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1505,c_1518]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2715,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2397,c_1499]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_19,negated_conjecture,
% 3.24/1.01      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.01      | v1_tops_2(sK2,sK1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_24,plain,
% 3.24/1.01      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | v1_tops_2(sK2,sK1) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_26,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2876,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_2715,c_23,c_24,c_26,c_59,c_1699,c_1820,c_2397]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3796,plain,
% 3.24/1.01      ( r2_hidden(X0,sK2) != iProver_top
% 3.24/1.01      | v3_pre_topc(X0,sK1) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_3252,c_23,c_1758,c_2876,c_3242,c_3505]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3797,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_3796]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3979,plain,
% 3.24/1.01      ( r2_hidden(X0,sK2) != iProver_top
% 3.24/1.01      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_3727,c_334,c_3505,c_3797]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3980,plain,
% 3.24/1.01      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_3979]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_13,plain,
% 3.24/1.01      ( v1_tops_2(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.24/1.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1509,plain,
% 3.24/1.01      ( v1_tops_2(X0,X1) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.24/1.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.24/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2304,plain,
% 3.24/1.01      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.24/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1509,c_1499]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3650,plain,
% 3.24/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_2304,c_23,c_59,c_1699]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3651,plain,
% 3.24/1.01      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_3650]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5589,plain,
% 3.24/1.01      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK1) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(demodulation,[status(thm)],[c_5575,c_3651]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_11,plain,
% 3.24/1.01      ( v1_tops_2(X0,X1)
% 3.24/1.01      | ~ v3_pre_topc(sK0(X1,X0),X1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1511,plain,
% 3.24/1.01      ( v1_tops_2(X0,X1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(X1,X0),X1) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.24/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5730,plain,
% 3.24/1.01      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_5575,c_1511]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_7558,plain,
% 3.24/1.01      ( v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_5589,c_23,c_59,c_1699,c_5730]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_7559,plain,
% 3.24/1.01      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_7558]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_7567,plain,
% 3.24/1.01      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | r2_hidden(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0),sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_3980,c_7559]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_7697,plain,
% 3.24/1.01      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_7686,c_7567]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5603,plain,
% 3.24/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.01      inference(demodulation,[status(thm)],[c_5575,c_1506]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_9,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_348,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.24/1.01      | ~ l1_pre_topc(X1)
% 3.24/1.01      | sK1 != X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_349,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK1)
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.24/1.01      | ~ l1_pre_topc(sK1) ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_348]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_353,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.01      | ~ v3_pre_topc(X0,sK1) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_349,c_20]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_354,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK1)
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_353]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1500,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK1) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2398,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK1) != iProver_top
% 3.24/1.01      | r2_hidden(X1,X0) != iProver_top
% 3.24/1.01      | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1500,c_1518]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2873,plain,
% 3.24/1.01      ( v1_tops_2(X0,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
% 3.24/1.01      | r2_hidden(X1,sK0(sK1,X0)) != iProver_top
% 3.24/1.01      | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1509,c_2398]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_605,plain,
% 3.24/1.01      ( v1_tops_2(X0,X1)
% 3.24/1.01      | ~ v3_pre_topc(sK0(X1,X0),X1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.24/1.01      | sK1 != X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_606,plain,
% 3.24/1.01      ( v1_tops_2(X0,sK1)
% 3.24/1.01      | ~ v3_pre_topc(sK0(sK1,X0),sK1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_605]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_607,plain,
% 3.24/1.01      ( v1_tops_2(X0,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_4750,plain,
% 3.24/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
% 3.24/1.01      | v1_tops_2(X0,sK1) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_2873,c_607]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_4751,plain,
% 3.24/1.01      ( v1_tops_2(X0,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(sK1,X0),sK1) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_4750]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6056,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_5603,c_4751]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1723,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1)
% 3.24/1.01      | ~ v3_pre_topc(sK0(sK1,sK2),sK1)
% 3.24/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.24/1.01      | ~ l1_pre_topc(sK1) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1724,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.24/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_1723]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6055,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(sK0(sK1,sK2),sK2) = iProver_top
% 3.24/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_5603,c_1510]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6407,plain,
% 3.24/1.01      ( r2_hidden(sK0(sK1,sK2),sK2) = iProver_top
% 3.24/1.01      | v1_tops_2(sK2,sK1) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_6055,c_23]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6408,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | r2_hidden(sK0(sK1,sK2),sK2) = iProver_top ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_6407]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6414,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK0(sK1,sK2),sK1) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_6408,c_3797]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6563,plain,
% 3.24/1.01      ( v1_tops_2(sK2,sK1) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_6056,c_23,c_1724,c_5603,c_6414]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_15,negated_conjecture,
% 3.24/1.01      ( ~ v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.24/1.01      | ~ v1_tops_2(sK2,sK1)
% 3.24/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.24/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.24/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1507,plain,
% 3.24/1.01      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v1_tops_2(sK2,sK1) != iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5605,plain,
% 3.24/1.01      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v1_tops_2(sK2,sK1) != iProver_top
% 3.24/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.24/1.01      inference(demodulation,[status(thm)],[c_5575,c_1507]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5618,plain,
% 3.24/1.01      ( v1_tops_2(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.24/1.01      | v1_tops_2(sK2,sK1) != iProver_top ),
% 3.24/1.01      inference(backward_subsumption_resolution,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_5603,c_5605]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(contradiction,plain,
% 3.24/1.01      ( $false ),
% 3.24/1.01      inference(minisat,[status(thm)],[c_7697,c_6563,c_5618,c_5603]) ).
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  ------                               Statistics
% 3.24/1.01  
% 3.24/1.01  ------ General
% 3.24/1.01  
% 3.24/1.01  abstr_ref_over_cycles:                  0
% 3.24/1.01  abstr_ref_under_cycles:                 0
% 3.24/1.01  gc_basic_clause_elim:                   0
% 3.24/1.01  forced_gc_time:                         0
% 3.24/1.01  parsing_time:                           0.013
% 3.24/1.01  unif_index_cands_time:                  0.
% 3.24/1.01  unif_index_add_time:                    0.
% 3.24/1.01  orderings_time:                         0.
% 3.24/1.01  out_proof_time:                         0.014
% 3.24/1.01  total_time:                             0.256
% 3.24/1.01  num_of_symbols:                         45
% 3.24/1.01  num_of_terms:                           5820
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing
% 3.24/1.01  
% 3.24/1.01  num_of_splits:                          0
% 3.24/1.01  num_of_split_atoms:                     0
% 3.24/1.01  num_of_reused_defs:                     0
% 3.24/1.01  num_eq_ax_congr_red:                    9
% 3.24/1.01  num_of_sem_filtered_clauses:            1
% 3.24/1.01  num_of_subtypes:                        0
% 3.24/1.01  monotx_restored_types:                  0
% 3.24/1.01  sat_num_of_epr_types:                   0
% 3.24/1.01  sat_num_of_non_cyclic_types:            0
% 3.24/1.01  sat_guarded_non_collapsed_types:        0
% 3.24/1.01  num_pure_diseq_elim:                    0
% 3.24/1.01  simp_replaced_by:                       0
% 3.24/1.01  res_preprocessed:                       110
% 3.24/1.01  prep_upred:                             0
% 3.24/1.01  prep_unflattend:                        38
% 3.24/1.01  smt_new_axioms:                         0
% 3.24/1.01  pred_elim_cands:                        6
% 3.24/1.01  pred_elim:                              1
% 3.24/1.01  pred_elim_cl:                           1
% 3.24/1.01  pred_elim_cycles:                       7
% 3.24/1.01  merged_defs:                            0
% 3.24/1.01  merged_defs_ncl:                        0
% 3.24/1.01  bin_hyper_res:                          0
% 3.24/1.01  prep_cycles:                            4
% 3.24/1.01  pred_elim_time:                         0.013
% 3.24/1.01  splitting_time:                         0.
% 3.24/1.01  sem_filter_time:                        0.
% 3.24/1.01  monotx_time:                            0.001
% 3.24/1.01  subtype_inf_time:                       0.
% 3.24/1.01  
% 3.24/1.01  ------ Problem properties
% 3.24/1.01  
% 3.24/1.01  clauses:                                21
% 3.24/1.01  conjectures:                            6
% 3.24/1.01  epr:                                    1
% 3.24/1.01  horn:                                   15
% 3.24/1.01  ground:                                 6
% 3.24/1.01  unary:                                  1
% 3.24/1.01  binary:                                 7
% 3.24/1.01  lits:                                   61
% 3.24/1.01  lits_eq:                                5
% 3.24/1.01  fd_pure:                                0
% 3.24/1.01  fd_pseudo:                              0
% 3.24/1.01  fd_cond:                                0
% 3.24/1.01  fd_pseudo_cond:                         2
% 3.24/1.01  ac_symbols:                             0
% 3.24/1.01  
% 3.24/1.01  ------ Propositional Solver
% 3.24/1.01  
% 3.24/1.01  prop_solver_calls:                      29
% 3.24/1.01  prop_fast_solver_calls:                 1227
% 3.24/1.01  smt_solver_calls:                       0
% 3.24/1.01  smt_fast_solver_calls:                  0
% 3.24/1.01  prop_num_of_clauses:                    2306
% 3.24/1.01  prop_preprocess_simplified:             6665
% 3.24/1.01  prop_fo_subsumed:                       65
% 3.24/1.01  prop_solver_time:                       0.
% 3.24/1.01  smt_solver_time:                        0.
% 3.24/1.01  smt_fast_solver_time:                   0.
% 3.24/1.01  prop_fast_solver_time:                  0.
% 3.24/1.01  prop_unsat_core_time:                   0.
% 3.24/1.01  
% 3.24/1.01  ------ QBF
% 3.24/1.01  
% 3.24/1.01  qbf_q_res:                              0
% 3.24/1.01  qbf_num_tautologies:                    0
% 3.24/1.01  qbf_prep_cycles:                        0
% 3.24/1.01  
% 3.24/1.01  ------ BMC1
% 3.24/1.01  
% 3.24/1.01  bmc1_current_bound:                     -1
% 3.24/1.01  bmc1_last_solved_bound:                 -1
% 3.24/1.01  bmc1_unsat_core_size:                   -1
% 3.24/1.01  bmc1_unsat_core_parents_size:           -1
% 3.24/1.01  bmc1_merge_next_fun:                    0
% 3.24/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.24/1.01  
% 3.24/1.01  ------ Instantiation
% 3.24/1.01  
% 3.24/1.01  inst_num_of_clauses:                    702
% 3.24/1.01  inst_num_in_passive:                    172
% 3.24/1.01  inst_num_in_active:                     451
% 3.24/1.01  inst_num_in_unprocessed:                79
% 3.24/1.01  inst_num_of_loops:                      490
% 3.24/1.01  inst_num_of_learning_restarts:          0
% 3.24/1.01  inst_num_moves_active_passive:          35
% 3.24/1.01  inst_lit_activity:                      0
% 3.24/1.01  inst_lit_activity_moves:                0
% 3.24/1.01  inst_num_tautologies:                   0
% 3.24/1.01  inst_num_prop_implied:                  0
% 3.24/1.01  inst_num_existing_simplified:           0
% 3.24/1.01  inst_num_eq_res_simplified:             0
% 3.24/1.01  inst_num_child_elim:                    0
% 3.24/1.01  inst_num_of_dismatching_blockings:      869
% 3.24/1.01  inst_num_of_non_proper_insts:           1436
% 3.24/1.01  inst_num_of_duplicates:                 0
% 3.24/1.01  inst_inst_num_from_inst_to_res:         0
% 3.24/1.01  inst_dismatching_checking_time:         0.
% 3.24/1.01  
% 3.24/1.01  ------ Resolution
% 3.24/1.01  
% 3.24/1.01  res_num_of_clauses:                     0
% 3.24/1.01  res_num_in_passive:                     0
% 3.24/1.01  res_num_in_active:                      0
% 3.24/1.01  res_num_of_loops:                       114
% 3.24/1.01  res_forward_subset_subsumed:            67
% 3.24/1.01  res_backward_subset_subsumed:           4
% 3.24/1.01  res_forward_subsumed:                   0
% 3.24/1.01  res_backward_subsumed:                  0
% 3.24/1.01  res_forward_subsumption_resolution:     3
% 3.24/1.01  res_backward_subsumption_resolution:    0
% 3.24/1.01  res_clause_to_clause_subsumption:       328
% 3.24/1.01  res_orphan_elimination:                 0
% 3.24/1.01  res_tautology_del:                      115
% 3.24/1.01  res_num_eq_res_simplified:              0
% 3.24/1.01  res_num_sel_changes:                    0
% 3.24/1.01  res_moves_from_active_to_pass:          0
% 3.24/1.01  
% 3.24/1.01  ------ Superposition
% 3.24/1.01  
% 3.24/1.01  sup_time_total:                         0.
% 3.24/1.01  sup_time_generating:                    0.
% 3.24/1.01  sup_time_sim_full:                      0.
% 3.24/1.01  sup_time_sim_immed:                     0.
% 3.24/1.01  
% 3.24/1.01  sup_num_of_clauses:                     98
% 3.24/1.01  sup_num_in_active:                      53
% 3.24/1.01  sup_num_in_passive:                     45
% 3.24/1.01  sup_num_of_loops:                       97
% 3.24/1.01  sup_fw_superposition:                   64
% 3.24/1.01  sup_bw_superposition:                   116
% 3.24/1.01  sup_immediate_simplified:               59
% 3.24/1.01  sup_given_eliminated:                   2
% 3.24/1.01  comparisons_done:                       0
% 3.24/1.01  comparisons_avoided:                    0
% 3.24/1.01  
% 3.24/1.01  ------ Simplifications
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  sim_fw_subset_subsumed:                 26
% 3.24/1.01  sim_bw_subset_subsumed:                 27
% 3.24/1.01  sim_fw_subsumed:                        16
% 3.24/1.01  sim_bw_subsumed:                        3
% 3.24/1.01  sim_fw_subsumption_res:                 2
% 3.24/1.01  sim_bw_subsumption_res:                 1
% 3.24/1.01  sim_tautology_del:                      13
% 3.24/1.01  sim_eq_tautology_del:                   15
% 3.24/1.01  sim_eq_res_simp:                        0
% 3.24/1.01  sim_fw_demodulated:                     1
% 3.24/1.01  sim_bw_demodulated:                     40
% 3.24/1.01  sim_light_normalised:                   18
% 3.24/1.01  sim_joinable_taut:                      0
% 3.24/1.01  sim_joinable_simp:                      0
% 3.24/1.01  sim_ac_normalised:                      0
% 3.24/1.01  sim_smt_subsumption:                    0
% 3.24/1.01  
%------------------------------------------------------------------------------
