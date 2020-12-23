%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1852+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:40 EST 2020

% Result     : Theorem 1.23s
% Output     : CNFRefutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 216 expanded)
%              Number of clauses        :   49 (  62 expanded)
%              Number of leaves         :    7 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  244 ( 970 expanded)
%              Number of equality atoms :   81 ( 227 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
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

fof(f16,plain,
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

fof(f18,plain,
    ( ~ v3_tdlat_3(sK2)
    & v3_tdlat_3(sK1)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17,f16])).

fof(f28,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
        & r2_hidden(sK0(X0),u1_pre_topc(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f19,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | r2_hidden(sK0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_9,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_709,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1065,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_709])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_20,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_22,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1066,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK1) = X1
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_709])).

cnf(c_1213,plain,
    ( u1_pre_topc(sK1) = X1
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1065,c_12,c_22,c_1066])).

cnf(c_1214,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK1) = X1 ),
    inference(renaming,[status(thm)],[c_1213])).

cnf(c_1219,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(equality_resolution,[status(thm)],[c_1214])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_pre_topc(sK1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1))
    | ~ v3_tdlat_3(sK1) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_8,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_179,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1))
    | ~ r2_hidden(X0,u1_pre_topc(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_175,c_8])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_pre_topc(sK1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1)) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_702,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(sK1),X0),u1_pre_topc(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1300,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(sK1),X0),u1_pre_topc(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1219,c_702])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_708,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1090,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_708])).

cnf(c_21,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1091,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_708])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1091])).

cnf(c_1231,plain,
    ( u1_struct_0(sK1) = X0
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1090,c_11,c_21,c_1108])).

cnf(c_1232,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(renaming,[status(thm)],[c_1231])).

cnf(c_1237,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(equality_resolution,[status(thm)],[c_1232])).

cnf(c_1499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),X0),u1_pre_topc(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1300,c_1237])).

cnf(c_0,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | v3_tdlat_3(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_148,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_149,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | v3_tdlat_3(sK2) ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_7,negated_conjecture,
    ( ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_151,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_149,c_7])).

cnf(c_704,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_1506,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK0(sK2),u1_pre_topc(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_704])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | v3_tdlat_3(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_137,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_138,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | v3_tdlat_3(sK2) ),
    inference(unflattening,[status(thm)],[c_137])).

cnf(c_139,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2)) = iProver_top
    | v3_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | v3_tdlat_3(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_126,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v3_tdlat_3(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_127,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tdlat_3(sK2) ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_128,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v3_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_15,plain,
    ( v3_tdlat_3(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1506,c_139,c_128,c_15])).


%------------------------------------------------------------------------------
