%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:45 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  133 (1009 expanded)
%              Number of clauses        :   98 ( 386 expanded)
%              Number of leaves         :   12 ( 199 expanded)
%              Depth                    :   20
%              Number of atoms          :  405 (4436 expanded)
%              Number of equality atoms :  158 ( 615 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) ) ) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v3_pre_topc(sK1,X0) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(sK1,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v3_pre_topc(X1,X0) ) ) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v3_pre_topc(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v3_pre_topc(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v3_pre_topc(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
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

fof(f9,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_410,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_418,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_420,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_907,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_418,c_420])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_423,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1098,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_907,c_423])).

cnf(c_627,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_628,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_675,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(resolution,[status(thm)],[c_3,c_5])).

cnf(c_676,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_690,plain,
    ( ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(resolution,[status(thm)],[c_4,c_5])).

cnf(c_691,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_1415,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1098,c_628,c_676,c_691])).

cnf(c_1416,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1415])).

cnf(c_1423,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(superposition,[status(thm)],[c_410,c_1416])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_417,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1439,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_417])).

cnf(c_1594,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0)
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1439])).

cnf(c_25,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_545,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_547,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_552,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_629,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_738,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | X1 = u1_pre_topc(sK0)
    | g1_pre_topc(X2,X1) != g1_pre_topc(X0,u1_pre_topc(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_842,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | X0 = u1_pre_topc(sK0)
    | g1_pre_topc(X1,X0) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2702,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1594,c_13,c_25,c_547,c_552,c_629,c_1232])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_414,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1180,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_414,c_421])).

cnf(c_1493,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_14,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_24,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_26,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_132,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_655,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_621,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK0))
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_727,plain,
    ( m1_subset_1(sK1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_773,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_966,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_141,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_774,plain,
    ( X0 != u1_struct_0(sK0)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_1047,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1166,plain,
    ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = k1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1198,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1180])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_413,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1181,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_421])).

cnf(c_12,negated_conjecture,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15,plain,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_546,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_548,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1317,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1181,c_14,c_15,c_26,c_548])).

cnf(c_1318,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1317])).

cnf(c_1319,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(sK1,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1318])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_416,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1437,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_416])).

cnf(c_1583,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0)
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1437])).

cnf(c_1601,plain,
    ( ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_13,c_14,c_8,c_25,c_26,c_547,c_655,c_966,c_1166,c_1198,c_1319,c_1583])).

cnf(c_1602,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(renaming,[status(thm)],[c_1601])).

cnf(c_1603,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_1717,plain,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1180,c_1603])).

cnf(c_1718,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1717])).

cnf(c_2707,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2702,c_1718])).

cnf(c_2006,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1583,c_14,c_26])).

cnf(c_2013,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2006,c_414])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | v3_pre_topc(X0,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2102,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_422])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_967,plain,
    ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != sK1
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_966])).

cnf(c_1753,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[status(thm)],[c_1,c_9])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_820,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK1,u1_pre_topc(X0))
    | v3_pre_topc(sK1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1700,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1908,plain,
    ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1753,c_13,c_14,c_11,c_25,c_26,c_547,c_655,c_966,c_1166,c_1583,c_1700])).

cnf(c_1909,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(renaming,[status(thm)],[c_1908])).

cnf(c_1910,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1909])).

cnf(c_140,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_639,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | X0 != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_746,plain,
    ( r2_hidden(sK1,u1_pre_topc(X0))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_2322,plain,
    ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_2323,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2322])).

cnf(c_2419,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2102,c_13,c_14,c_19,c_25,c_26,c_547,c_552,c_629,c_655,c_967,c_1166,c_1232,c_1583,c_1910,c_2013,c_2323])).

cnf(c_2103,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_421])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2707,c_2419,c_2103,c_15,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.95/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.00  
% 2.95/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.95/1.00  
% 2.95/1.00  ------  iProver source info
% 2.95/1.00  
% 2.95/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.95/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.95/1.00  git: non_committed_changes: false
% 2.95/1.00  git: last_make_outside_of_git: false
% 2.95/1.00  
% 2.95/1.00  ------ 
% 2.95/1.00  ------ Parsing...
% 2.95/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.95/1.00  
% 2.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.95/1.00  
% 2.95/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.95/1.00  
% 2.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.95/1.00  ------ Proving...
% 2.95/1.00  ------ Problem Properties 
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  clauses                                 14
% 2.95/1.00  conjectures                             6
% 2.95/1.00  EPR                                     1
% 2.95/1.00  Horn                                    10
% 2.95/1.00  unary                                   1
% 2.95/1.00  binary                                  7
% 2.95/1.00  lits                                    36
% 2.95/1.00  lits eq                                 5
% 2.95/1.00  fd_pure                                 0
% 2.95/1.00  fd_pseudo                               0
% 2.95/1.00  fd_cond                                 0
% 2.95/1.00  fd_pseudo_cond                          2
% 2.95/1.00  AC symbols                              0
% 2.95/1.00  
% 2.95/1.00  ------ Input Options Time Limit: Unbounded
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  ------ 
% 2.95/1.00  Current options:
% 2.95/1.00  ------ 
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  ------ Proving...
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  % SZS status Theorem for theBenchmark.p
% 2.95/1.00  
% 2.95/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.95/1.00  
% 2.95/1.00  fof(f6,conjecture,(
% 2.95/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f7,negated_conjecture,(
% 2.95/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.95/1.00    inference(negated_conjecture,[],[f6])).
% 2.95/1.00  
% 2.95/1.00  fof(f8,plain,(
% 2.95/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.95/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.95/1.00  
% 2.95/1.00  fof(f15,plain,(
% 2.95/1.00    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 2.95/1.00    inference(ennf_transformation,[],[f8])).
% 2.95/1.00  
% 2.95/1.00  fof(f17,plain,(
% 2.95/1.00    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)))) & l1_pre_topc(X0))),
% 2.95/1.00    inference(nnf_transformation,[],[f15])).
% 2.95/1.00  
% 2.95/1.00  fof(f18,plain,(
% 2.95/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)))) & l1_pre_topc(X0))),
% 2.95/1.00    inference(flattening,[],[f17])).
% 2.95/1.00  
% 2.95/1.00  fof(f20,plain,(
% 2.95/1.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(sK1,X0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(sK1,X0))))) )),
% 2.95/1.00    introduced(choice_axiom,[])).
% 2.95/1.00  
% 2.95/1.00  fof(f19,plain,(
% 2.95/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v3_pre_topc(X1,sK0)))) & l1_pre_topc(sK0))),
% 2.95/1.00    introduced(choice_axiom,[])).
% 2.95/1.00  
% 2.95/1.00  fof(f21,plain,(
% 2.95/1.00    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v3_pre_topc(sK1,sK0)))) & l1_pre_topc(sK0)),
% 2.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 2.95/1.00  
% 2.95/1.00  fof(f30,plain,(
% 2.95/1.00    l1_pre_topc(sK0)),
% 2.95/1.00    inference(cnf_transformation,[],[f21])).
% 2.95/1.00  
% 2.95/1.00  fof(f4,axiom,(
% 2.95/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f13,plain,(
% 2.95/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/1.00    inference(ennf_transformation,[],[f4])).
% 2.95/1.00  
% 2.95/1.00  fof(f27,plain,(
% 2.95/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f13])).
% 2.95/1.00  
% 2.95/1.00  fof(f3,axiom,(
% 2.95/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f12,plain,(
% 2.95/1.00    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.95/1.00    inference(ennf_transformation,[],[f3])).
% 2.95/1.00  
% 2.95/1.00  fof(f26,plain,(
% 2.95/1.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f12])).
% 2.95/1.00  
% 2.95/1.00  fof(f1,axiom,(
% 2.95/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f9,plain,(
% 2.95/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.95/1.00    inference(ennf_transformation,[],[f1])).
% 2.95/1.00  
% 2.95/1.00  fof(f10,plain,(
% 2.95/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.95/1.00    inference(flattening,[],[f9])).
% 2.95/1.00  
% 2.95/1.00  fof(f22,plain,(
% 2.95/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f10])).
% 2.95/1.00  
% 2.95/1.00  fof(f25,plain,(
% 2.95/1.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f12])).
% 2.95/1.00  
% 2.95/1.00  fof(f5,axiom,(
% 2.95/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f14,plain,(
% 2.95/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.95/1.00    inference(ennf_transformation,[],[f5])).
% 2.95/1.00  
% 2.95/1.00  fof(f29,plain,(
% 2.95/1.00    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f14])).
% 2.95/1.00  
% 2.95/1.00  fof(f34,plain,(
% 2.95/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.95/1.00    inference(cnf_transformation,[],[f21])).
% 2.95/1.00  
% 2.95/1.00  fof(f2,axiom,(
% 2.95/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f11,plain,(
% 2.95/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/1.00    inference(ennf_transformation,[],[f2])).
% 2.95/1.00  
% 2.95/1.00  fof(f16,plain,(
% 2.95/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.95/1.00    inference(nnf_transformation,[],[f11])).
% 2.95/1.00  
% 2.95/1.00  fof(f23,plain,(
% 2.95/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f16])).
% 2.95/1.00  
% 2.95/1.00  fof(f35,plain,(
% 2.95/1.00    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 2.95/1.00    inference(cnf_transformation,[],[f21])).
% 2.95/1.00  
% 2.95/1.00  fof(f33,plain,(
% 2.95/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v3_pre_topc(sK1,sK0)),
% 2.95/1.00    inference(cnf_transformation,[],[f21])).
% 2.95/1.00  
% 2.95/1.00  fof(f31,plain,(
% 2.95/1.00    v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v3_pre_topc(sK1,sK0)),
% 2.95/1.00    inference(cnf_transformation,[],[f21])).
% 2.95/1.00  
% 2.95/1.00  fof(f28,plain,(
% 2.95/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f14])).
% 2.95/1.00  
% 2.95/1.00  fof(f24,plain,(
% 2.95/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f16])).
% 2.95/1.00  
% 2.95/1.00  fof(f32,plain,(
% 2.95/1.00    v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.95/1.00    inference(cnf_transformation,[],[f21])).
% 2.95/1.00  
% 2.95/1.00  cnf(c_13,negated_conjecture,
% 2.95/1.00      ( l1_pre_topc(sK0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_410,plain,
% 2.95/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5,plain,
% 2.95/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.95/1.00      | ~ l1_pre_topc(X0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f27]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_418,plain,
% 2.95/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.95/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_3,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.95/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_420,plain,
% 2.95/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_907,plain,
% 2.95/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_418,c_420]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_0,plain,
% 2.95/1.00      ( ~ l1_pre_topc(X0)
% 2.95/1.00      | ~ v1_pre_topc(X0)
% 2.95/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.95/1.00      inference(cnf_transformation,[],[f22]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_423,plain,
% 2.95/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.95/1.00      | l1_pre_topc(X0) != iProver_top
% 2.95/1.00      | v1_pre_topc(X0) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1098,plain,
% 2.95/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.95/1.00      | l1_pre_topc(X0) != iProver_top
% 2.95/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_907,c_423]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_627,plain,
% 2.95/1.00      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.95/1.00      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.95/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_628,plain,
% 2.95/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.95/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_675,plain,
% 2.95/1.00      ( ~ l1_pre_topc(X0)
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.95/1.00      inference(resolution,[status(thm)],[c_3,c_5]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_676,plain,
% 2.95/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_4,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.95/1.00      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.95/1.00      inference(cnf_transformation,[],[f25]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_690,plain,
% 2.95/1.00      ( ~ l1_pre_topc(X0)
% 2.95/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.95/1.00      inference(resolution,[status(thm)],[c_4,c_5]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_691,plain,
% 2.95/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.95/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1415,plain,
% 2.95/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.95/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1098,c_628,c_676,c_691]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1416,plain,
% 2.95/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.95/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.95/1.00      inference(renaming,[status(thm)],[c_1415]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1423,plain,
% 2.95/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_410,c_1416]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_6,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.95/1.00      | X2 = X0
% 2.95/1.00      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_417,plain,
% 2.95/1.00      ( X0 = X1
% 2.95/1.00      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 2.95/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1439,plain,
% 2.95/1.00      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 2.95/1.00      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
% 2.95/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1423,c_417]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1594,plain,
% 2.95/1.00      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0)
% 2.95/1.00      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.95/1.00      inference(equality_resolution,[status(thm)],[c_1439]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_25,plain,
% 2.95/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.95/1.00      | ~ l1_pre_topc(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_545,plain,
% 2.95/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_547,plain,
% 2.95/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_545]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_550,plain,
% 2.95/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.95/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_552,plain,
% 2.95/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.95/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_550]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_629,plain,
% 2.95/1.00      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_627]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_738,plain,
% 2.95/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.95/1.00      | X1 = u1_pre_topc(sK0)
% 2.95/1.00      | g1_pre_topc(X2,X1) != g1_pre_topc(X0,u1_pre_topc(sK0)) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_842,plain,
% 2.95/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.95/1.00      | X0 = u1_pre_topc(sK0)
% 2.95/1.00      | g1_pre_topc(X1,X0) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_738]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1232,plain,
% 2.95/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.95/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
% 2.95/1.00      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_842]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2702,plain,
% 2.95/1.00      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(sK0) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1594,c_13,c_25,c_547,c_552,c_629,c_1232]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_9,negated_conjecture,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 2.95/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.95/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_414,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 2.95/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.95/1.00      | ~ v3_pre_topc(X0,X1)
% 2.95/1.00      | ~ l1_pre_topc(X1) ),
% 2.95/1.00      inference(cnf_transformation,[],[f23]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_421,plain,
% 2.95/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.95/1.00      | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 2.95/1.00      | v3_pre_topc(X0,X1) != iProver_top
% 2.95/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1180,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_414,c_421]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1493,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(resolution,[status(thm)],[c_2,c_9]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_14,plain,
% 2.95/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_8,negated_conjecture,
% 2.95/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 2.95/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | ~ v3_pre_topc(sK1,sK0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_24,plain,
% 2.95/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.95/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_26,plain,
% 2.95/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.95/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_132,plain,( X0 = X0 ),theory(equality) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_655,plain,
% 2.95/1.00      ( sK1 = sK1 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_132]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_142,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.95/1.00      theory(equality) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_621,plain,
% 2.95/1.00      ( m1_subset_1(X0,X1)
% 2.95/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | X1 != k1_zfmisc_1(u1_struct_0(sK0))
% 2.95/1.00      | X0 != sK1 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_142]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_727,plain,
% 2.95/1.00      ( m1_subset_1(sK1,X0)
% 2.95/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | X0 != k1_zfmisc_1(u1_struct_0(sK0))
% 2.95/1.00      | sK1 != sK1 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_621]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_773,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(X0))
% 2.95/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK0))
% 2.95/1.00      | sK1 != sK1 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_727]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_966,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 2.95/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != k1_zfmisc_1(u1_struct_0(sK0))
% 2.95/1.00      | sK1 != sK1 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_773]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_141,plain,
% 2.95/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.95/1.00      theory(equality) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_774,plain,
% 2.95/1.00      ( X0 != u1_struct_0(sK0)
% 2.95/1.00      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_141]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1047,plain,
% 2.95/1.00      ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK0))
% 2.95/1.00      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_774]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1166,plain,
% 2.95/1.00      ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = k1_zfmisc_1(u1_struct_0(sK0))
% 2.95/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_1047]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1198,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1180]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_10,negated_conjecture,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 2.95/1.00      | v3_pre_topc(sK1,sK0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_413,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1181,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,sK0) = iProver_top
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_413,c_421]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_12,negated_conjecture,
% 2.95/1.00      ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | v3_pre_topc(sK1,sK0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_15,plain,
% 2.95/1.00      ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_546,plain,
% 2.95/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_548,plain,
% 2.95/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.95/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_546]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1317,plain,
% 2.95/1.00      ( v3_pre_topc(sK1,sK0) = iProver_top
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1181,c_14,c_15,c_26,c_548]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1318,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 2.95/1.00      inference(renaming,[status(thm)],[c_1317]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1319,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | v3_pre_topc(sK1,sK0) ),
% 2.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1318]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_7,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.95/1.00      | X2 = X1
% 2.95/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_416,plain,
% 2.95/1.00      ( X0 = X1
% 2.95/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.95/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1437,plain,
% 2.95/1.00      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 2.95/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 2.95/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1423,c_416]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1583,plain,
% 2.95/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0)
% 2.95/1.00      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.95/1.00      inference(equality_resolution,[status(thm)],[c_1437]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1601,plain,
% 2.95/1.00      ( ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1493,c_13,c_14,c_8,c_25,c_26,c_547,c_655,c_966,c_1166,
% 2.95/1.00                 c_1198,c_1319,c_1583]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1602,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(renaming,[status(thm)],[c_1601]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1603,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1717,plain,
% 2.95/1.00      ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1180,c_1603]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1718,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.95/1.00      inference(renaming,[status(thm)],[c_1717]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2707,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 2.95/1.00      inference(demodulation,[status(thm)],[c_2702,c_1718]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2006,plain,
% 2.95/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1583,c_14,c_26]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2013,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.95/1.00      inference(demodulation,[status(thm)],[c_2006,c_414]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.95/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.95/1.00      | v3_pre_topc(X0,X1)
% 2.95/1.00      | ~ l1_pre_topc(X1) ),
% 2.95/1.00      inference(cnf_transformation,[],[f24]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_422,plain,
% 2.95/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.95/1.00      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 2.95/1.00      | v3_pre_topc(X0,X1) = iProver_top
% 2.95/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2102,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,sK0) = iProver_top
% 2.95/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_2013,c_422]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_19,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 2.95/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_967,plain,
% 2.95/1.00      ( k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != k1_zfmisc_1(u1_struct_0(sK0))
% 2.95/1.00      | sK1 != sK1
% 2.95/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 2.95/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_966]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1753,plain,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(resolution,[status(thm)],[c_1,c_9]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_11,negated_conjecture,
% 2.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_820,plain,
% 2.95/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.95/1.00      | ~ r2_hidden(sK1,u1_pre_topc(X0))
% 2.95/1.00      | v3_pre_topc(sK1,X0)
% 2.95/1.00      | ~ l1_pre_topc(X0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1700,plain,
% 2.95/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 2.95/1.00      | ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_820]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1908,plain,
% 2.95/1.00      ( v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.95/1.00      | ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1753,c_13,c_14,c_11,c_25,c_26,c_547,c_655,c_966,
% 2.95/1.00                 c_1166,c_1583,c_1700]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1909,plain,
% 2.95/1.00      ( ~ r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 2.95/1.00      inference(renaming,[status(thm)],[c_1908]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1910,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1909]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_140,plain,
% 2.95/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | X2 != X1 ),
% 2.95/1.00      theory(equality) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_639,plain,
% 2.95/1.00      ( r2_hidden(sK1,X0)
% 2.95/1.00      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.95/1.00      | X0 != u1_pre_topc(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_140]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_746,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(X0))
% 2.95/1.00      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.95/1.00      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_639]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2322,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 2.95/1.00      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.95/1.00      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_pre_topc(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_746]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2323,plain,
% 2.95/1.00      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_pre_topc(sK0)
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 2.95/1.00      | r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_2322]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2419,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(sK0)) != iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_2102,c_13,c_14,c_19,c_25,c_26,c_547,c_552,c_629,c_655,
% 2.95/1.00                 c_967,c_1166,c_1232,c_1583,c_1910,c_2013,c_2323]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2103,plain,
% 2.95/1.00      ( r2_hidden(sK1,u1_pre_topc(sK0)) = iProver_top
% 2.95/1.00      | v3_pre_topc(sK1,sK0) != iProver_top
% 2.95/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_2013,c_421]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(contradiction,plain,
% 2.95/1.00      ( $false ),
% 2.95/1.00      inference(minisat,[status(thm)],[c_2707,c_2419,c_2103,c_15,c_14]) ).
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.95/1.00  
% 2.95/1.00  ------                               Statistics
% 2.95/1.00  
% 2.95/1.00  ------ Selected
% 2.95/1.00  
% 2.95/1.00  total_time:                             0.12
% 2.95/1.00  
%------------------------------------------------------------------------------
