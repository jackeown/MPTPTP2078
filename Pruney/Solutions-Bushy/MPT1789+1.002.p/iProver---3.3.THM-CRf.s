%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1789+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:25 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 543 expanded)
%              Number of clauses        :   56 ( 143 expanded)
%              Number of leaves         :   11 ( 146 expanded)
%              Depth                    :   16
%              Number of atoms          :  297 (2714 expanded)
%              Number of equality atoms :  110 ( 940 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
              & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) != k5_tmap_1(X0,X1)
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) != k5_tmap_1(X0,X1)
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) != k5_tmap_1(X0,X1)
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( u1_pre_topc(k6_tmap_1(X0,sK1)) != k5_tmap_1(X0,sK1)
          | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,sK1)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( u1_pre_topc(k6_tmap_1(X0,X1)) != k5_tmap_1(X0,X1)
              | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( u1_pre_topc(k6_tmap_1(sK0,X1)) != k5_tmap_1(sK0,X1)
            | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK1)
      | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK1)
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_469,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_11,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_170,c_11,c_10])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK0,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_174])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_210,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_206,c_11,c_10])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_11,c_10,c_206])).

cnf(c_466,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_653,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_469,c_466])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_11,c_10])).

cnf(c_467,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_554,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_469,c_467])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_471,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_853,plain,
    ( k5_tmap_1(sK0,sK1) = X0
    | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_471])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_224,c_11,c_10])).

cnf(c_515,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_516,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_855,plain,
    ( k5_tmap_1(sK0,sK1) = X0
    | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
    | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_471])).

cnf(c_963,plain,
    ( g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
    | k5_tmap_1(sK0,sK1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_16,c_516,c_855])).

cnf(c_964,plain,
    ( k5_tmap_1(sK0,sK1) = X0
    | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_963])).

cnf(c_969,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_653,c_964])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_470,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_732,plain,
    ( g1_pre_topc(X0,X1) != k6_tmap_1(sK0,sK1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_470])).

cnf(c_734,plain,
    ( g1_pre_topc(X0,X1) != k6_tmap_1(sK0,sK1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_470])).

cnf(c_895,plain,
    ( u1_struct_0(sK0) = X0
    | g1_pre_topc(X0,X1) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_16,c_516,c_734])).

cnf(c_896,plain,
    ( g1_pre_topc(X0,X1) != k6_tmap_1(sK0,sK1)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_895])).

cnf(c_901,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_653,c_896])).

cnf(c_346,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_525,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) != X0
    | u1_struct_0(sK0) != X0
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_578,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) != u1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_345,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_362,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_347,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_354,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_8,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK1)
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_969,c_901,c_578,c_362,c_354,c_8])).


%------------------------------------------------------------------------------
