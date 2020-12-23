%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:08 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  113 (1477 expanded)
%              Number of clauses        :   77 ( 556 expanded)
%              Number of leaves         :    8 ( 270 expanded)
%              Depth                    :   21
%              Number of atoms          :  354 (6415 expanded)
%              Number of equality atoms :  149 ( 901 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f9,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f19,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f21,plain,(
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
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
          | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          | ~ v1_tops_2(sK1,X0) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(sK1,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
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
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            | ~ v1_tops_2(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & v1_tops_2(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
      | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & v1_tops_2(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_410,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_420,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_953,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_422])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_423,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2397,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_423])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_828,plain,
    ( ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_829,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_2498,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2397,c_829])).

cnf(c_2499,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2498])).

cnf(c_2506,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(superposition,[status(thm)],[c_410,c_2499])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_418,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2541,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_418])).

cnf(c_14,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_30,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_32,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_545,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_546,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_548,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_2815,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2820,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_2912,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_14,c_32,c_548,c_2820])).

cnf(c_2913,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ),
    inference(renaming,[status(thm)],[c_2912])).

cnf(c_2919,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_2913])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_417,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | v1_tops_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5137,plain,
    ( r1_tarski(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2919,c_417])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_419,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2542,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_419])).

cnf(c_31,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_547,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_2543,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_419])).

cnf(c_2600,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2543])).

cnf(c_2893,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2542,c_13,c_31,c_547,c_2600,c_2815])).

cnf(c_2894,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ),
    inference(renaming,[status(thm)],[c_2893])).

cnf(c_2900,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0) ),
    inference(equality_resolution,[status(thm)],[c_2894])).

cnf(c_5152,plain,
    ( r1_tarski(X0,u1_pre_topc(sK0)) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5137,c_2900])).

cnf(c_6472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | r1_tarski(X0,u1_pre_topc(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5152,c_14,c_32,c_548])).

cnf(c_6473,plain,
    ( r1_tarski(X0,u1_pre_topc(sK0)) != iProver_top
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6472])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_414,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5099,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2919,c_414])).

cnf(c_8,negated_conjecture,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_415,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5101,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2919,c_415])).

cnf(c_5114,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5099,c_5101])).

cnf(c_644,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_645,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0)) != iProver_top
    | v1_tops_2(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_10,negated_conjecture,
    ( v1_tops_2(sK1,sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_413,plain,
    ( v1_tops_2(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( r1_tarski(X0,u1_pre_topc(X1))
    | ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_416,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
    | v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_795,plain,
    ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(sK1,sK0) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_416])).

cnf(c_12,negated_conjecture,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v1_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1407,plain,
    ( v1_tops_2(sK1,sK0) = iProver_top
    | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_14,c_15,c_32,c_548])).

cnf(c_1408,plain,
    ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v1_tops_2(sK1,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1407])).

cnf(c_3840,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top
    | v1_tops_2(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2900,c_1408])).

cnf(c_590,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_591,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_794,plain,
    ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_414,c_416])).

cnf(c_11,negated_conjecture,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1414,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_14,c_16,c_32,c_548])).

cnf(c_1415,plain,
    ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_1414])).

cnf(c_3839,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2900,c_1415])).

cnf(c_4559,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3840,c_14,c_591,c_3839])).

cnf(c_5369,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5114,c_14,c_591,c_645,c_3839,c_3840,c_5099])).

cnf(c_6481,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_5369])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6481,c_5099,c_4559])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.30/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/0.99  
% 3.30/0.99  ------  iProver source info
% 3.30/0.99  
% 3.30/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.30/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/0.99  git: non_committed_changes: false
% 3.30/0.99  git: last_make_outside_of_git: false
% 3.30/0.99  
% 3.30/0.99  ------ 
% 3.30/0.99  ------ Parsing...
% 3.30/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/0.99  ------ Proving...
% 3.30/0.99  ------ Problem Properties 
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  clauses                                 14
% 3.30/0.99  conjectures                             6
% 3.30/0.99  EPR                                     1
% 3.30/0.99  Horn                                    10
% 3.30/0.99  unary                                   1
% 3.30/0.99  binary                                  7
% 3.30/0.99  lits                                    36
% 3.30/0.99  lits eq                                 5
% 3.30/0.99  fd_pure                                 0
% 3.30/0.99  fd_pseudo                               0
% 3.30/0.99  fd_cond                                 0
% 3.30/0.99  fd_pseudo_cond                          2
% 3.30/0.99  AC symbols                              0
% 3.30/0.99  
% 3.30/0.99  ------ Input Options Time Limit: Unbounded
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  ------ 
% 3.30/0.99  Current options:
% 3.30/0.99  ------ 
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  ------ Proving...
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  % SZS status Theorem for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  fof(f6,conjecture,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f7,negated_conjecture,(
% 3.30/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.30/0.99    inference(negated_conjecture,[],[f6])).
% 3.30/0.99  
% 3.30/0.99  fof(f8,plain,(
% 3.30/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.30/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.30/0.99  
% 3.30/0.99  fof(f9,plain,(
% 3.30/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.30/0.99    inference(pure_predicate_removal,[],[f8])).
% 3.30/0.99  
% 3.30/0.99  fof(f16,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f9])).
% 3.30/0.99  
% 3.30/0.99  fof(f18,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0))),
% 3.30/0.99    inference(nnf_transformation,[],[f16])).
% 3.30/0.99  
% 3.30/0.99  fof(f19,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f18])).
% 3.30/0.99  
% 3.30/0.99  fof(f21,plain,(
% 3.30/0.99    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK1,X0)) & ((m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(sK1,X0))))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f20,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(X1,sK0)))) & l1_pre_topc(sK0))),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f22,plain,(
% 3.30/0.99    ((~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(sK1,sK0)))) & l1_pre_topc(sK0)),
% 3.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).
% 3.30/0.99  
% 3.30/0.99  fof(f31,plain,(
% 3.30/0.99    l1_pre_topc(sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f3,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f13,plain,(
% 3.30/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f3])).
% 3.30/0.99  
% 3.30/0.99  fof(f26,plain,(
% 3.30/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f13])).
% 3.30/0.99  
% 3.30/0.99  fof(f2,axiom,(
% 3.30/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f12,plain,(
% 3.30/0.99    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.30/0.99    inference(ennf_transformation,[],[f2])).
% 3.30/0.99  
% 3.30/0.99  fof(f25,plain,(
% 3.30/0.99    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f12])).
% 3.30/0.99  
% 3.30/0.99  fof(f1,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f10,plain,(
% 3.30/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f1])).
% 3.30/0.99  
% 3.30/0.99  fof(f11,plain,(
% 3.30/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f10])).
% 3.30/0.99  
% 3.30/0.99  fof(f23,plain,(
% 3.30/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f11])).
% 3.30/0.99  
% 3.30/0.99  fof(f24,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f12])).
% 3.30/0.99  
% 3.30/0.99  fof(f4,axiom,(
% 3.30/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f14,plain,(
% 3.30/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.30/0.99    inference(ennf_transformation,[],[f4])).
% 3.30/0.99  
% 3.30/0.99  fof(f27,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f14])).
% 3.30/0.99  
% 3.30/0.99  fof(f5,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f15,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f5])).
% 3.30/0.99  
% 3.30/0.99  fof(f17,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(nnf_transformation,[],[f15])).
% 3.30/0.99  
% 3.30/0.99  fof(f30,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f17])).
% 3.30/0.99  
% 3.30/0.99  fof(f28,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f14])).
% 3.30/0.99  
% 3.30/0.99  fof(f35,plain,(
% 3.30/0.99    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f36,plain,(
% 3.30/0.99    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f34,plain,(
% 3.30/0.99    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | v1_tops_2(sK1,sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f29,plain,(
% 3.30/0.99    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f17])).
% 3.30/0.99  
% 3.30/0.99  fof(f32,plain,(
% 3.30/0.99    v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_tops_2(sK1,sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f33,plain,(
% 3.30/0.99    v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  cnf(c_13,negated_conjecture,
% 3.30/0.99      ( l1_pre_topc(sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_410,plain,
% 3.30/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.30/0.99      | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_420,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_422,plain,
% 3.30/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_953,plain,
% 3.30/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_420,c_422]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_0,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0)
% 3.30/0.99      | ~ v1_pre_topc(X0)
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.30/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_423,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_pre_topc(X0) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2397,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_953,c_423]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.30/0.99      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_828,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0)
% 3.30/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.30/0.99      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_829,plain,
% 3.30/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2498,plain,
% 3.30/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2397,c_829]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2499,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_2498]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2506,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_410,c_2499]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.30/0.99      | X2 = X1
% 3.30/0.99      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_418,plain,
% 3.30/0.99      ( X0 = X1
% 3.30/0.99      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.30/0.99      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2541,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 3.30/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 3.30/0.99      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2506,c_418]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_14,plain,
% 3.30/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_30,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_32,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_545,plain,
% 3.30/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_546,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_548,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_546]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2815,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.30/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2820,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2815]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2912,plain,
% 3.30/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 3.30/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2541,c_14,c_32,c_548,c_2820]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2913,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 3.30/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_2912]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2919,plain,
% 3.30/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
% 3.30/0.99      inference(equality_resolution,[status(thm)],[c_2913]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6,plain,
% 3.30/0.99      ( ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.30/0.99      | v1_tops_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_417,plain,
% 3.30/0.99      ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
% 3.30/0.99      | v1_tops_2(X0,X1) = iProver_top
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5137,plain,
% 3.30/0.99      ( r1_tarski(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.30/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2919,c_417]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.30/0.99      | X2 = X0
% 3.30/0.99      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_419,plain,
% 3.30/0.99      ( X0 = X1
% 3.30/0.99      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 3.30/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2542,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 3.30/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
% 3.30/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2506,c_419]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_31,plain,
% 3.30/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.30/0.99      | ~ l1_pre_topc(sK0) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_547,plain,
% 3.30/0.99      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_545]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2543,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 3.30/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
% 3.30/0.99      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2506,c_419]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2600,plain,
% 3.30/0.99      ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 3.30/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ),
% 3.30/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2543]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2893,plain,
% 3.30/0.99      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
% 3.30/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2542,c_13,c_31,c_547,c_2600,c_2815]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2894,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 3.30/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_2893]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2900,plain,
% 3.30/0.99      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0) ),
% 3.30/0.99      inference(equality_resolution,[status(thm)],[c_2894]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5152,plain,
% 3.30/0.99      ( r1_tarski(X0,u1_pre_topc(sK0)) != iProver_top
% 3.30/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.30/0.99      inference(light_normalisation,[status(thm)],[c_5137,c_2900]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6472,plain,
% 3.30/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.30/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.30/0.99      | r1_tarski(X0,u1_pre_topc(sK0)) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_5152,c_14,c_32,c_548]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6473,plain,
% 3.30/0.99      ( r1_tarski(X0,u1_pre_topc(sK0)) != iProver_top
% 3.30/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_6472]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_9,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_414,plain,
% 3.30/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5099,plain,
% 3.30/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_2919,c_414]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_8,negated_conjecture,
% 3.30/0.99      ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.30/0.99      | ~ v1_tops_2(sK1,sK0)
% 3.30/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 3.30/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_415,plain,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5101,plain,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_2919,c_415]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5114,plain,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) != iProver_top ),
% 3.30/0.99      inference(backward_subsumption_resolution,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_5099,c_5101]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_644,plain,
% 3.30/0.99      ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
% 3.30/0.99      | v1_tops_2(sK1,sK0)
% 3.30/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.30/0.99      | ~ l1_pre_topc(sK0) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_645,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(sK0)) != iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) = iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10,negated_conjecture,
% 3.30/0.99      ( v1_tops_2(sK1,sK0)
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_413,plain,
% 3.30/0.99      ( v1_tops_2(sK1,sK0) = iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7,plain,
% 3.30/0.99      ( r1_tarski(X0,u1_pre_topc(X1))
% 3.30/0.99      | ~ v1_tops_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_416,plain,
% 3.30/0.99      ( r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
% 3.30/0.99      | v1_tops_2(X0,X1) != iProver_top
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_795,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 3.30/0.99      | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) = iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_413,c_416]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_12,negated_conjecture,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.30/0.99      | v1_tops_2(sK1,sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_15,plain,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1407,plain,
% 3.30/0.99      ( v1_tops_2(sK1,sK0) = iProver_top
% 3.30/0.99      | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_795,c_14,c_15,c_32,c_548]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1408,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) = iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_1407]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3840,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) = iProver_top ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_2900,c_1408]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_590,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(sK0))
% 3.30/0.99      | ~ v1_tops_2(sK1,sK0)
% 3.30/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.30/0.99      | ~ l1_pre_topc(sK0) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_591,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top
% 3.30/0.99      | v1_tops_2(sK1,sK0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_794,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 3.30/0.99      | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.30/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_414,c_416]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_11,negated_conjecture,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_16,plain,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1414,plain,
% 3.30/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.30/0.99      | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_794,c_14,c_16,c_32,c_548]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1415,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_1414]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3839,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_2900,c_1415]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4559,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(sK0)) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3840,c_14,c_591,c_3839]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5369,plain,
% 3.30/0.99      ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_5114,c_14,c_591,c_645,c_3839,c_3840,c_5099]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6481,plain,
% 3.30/0.99      ( r1_tarski(sK1,u1_pre_topc(sK0)) != iProver_top
% 3.30/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_6473,c_5369]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(contradiction,plain,
% 3.30/0.99      ( $false ),
% 3.30/0.99      inference(minisat,[status(thm)],[c_6481,c_5099,c_4559]) ).
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  ------                               Statistics
% 3.30/0.99  
% 3.30/0.99  ------ Selected
% 3.30/0.99  
% 3.30/0.99  total_time:                             0.248
% 3.30/0.99  
%------------------------------------------------------------------------------
