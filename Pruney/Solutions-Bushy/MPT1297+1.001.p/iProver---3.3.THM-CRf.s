%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1297+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:22 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 106 expanded)
%              Number of clauses        :   23 (  29 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 486 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
           => v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
            <=> v1_finset_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <~> v1_finset_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ v1_finset_1(sK1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),sK1)) )
        & ( v1_finset_1(sK1)
          | v1_finset_1(k7_setfam_1(u1_struct_0(X0),sK1)) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_finset_1(X1)
              | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & ( v1_finset_1(X1)
              | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( ~ v1_finset_1(sK1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & ( v1_finset_1(sK1)
      | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f19,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,
    ( v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_185,plain,
    ( ~ v1_finset_1(X0_36)
    | v1_finset_1(X1_36)
    | X1_36 != X0_36 ),
    theory(equality)).

cnf(c_394,plain,
    ( ~ v1_finset_1(X0_36)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != X0_36 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_396,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ v1_finset_1(sK1)
    | k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_178,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(k1_zfmisc_1(X0_37)))
    | k7_setfam_1(X0_37,k7_setfam_1(X0_37,X0_36)) = X0_36 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_360,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_179,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(k1_zfmisc_1(X0_37)))
    | m1_subset_1(k7_setfam_1(X0_37,X0_36),k1_zfmisc_1(k1_zfmisc_1(X0_37))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_357,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | v1_finset_1(X0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_finset_1(X0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X1),X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_102,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_finset_1(X0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X0)) ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_finset_1(X0_36)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X0_36)) ),
    inference(subtyping,[status(esa)],[c_102])).

cnf(c_349,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_4,negated_conjecture,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_54,plain,
    ( v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_55,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | v1_finset_1(sK1) ),
    inference(renaming,[status(thm)],[c_54])).

cnf(c_5,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_104,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | v1_finset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_129,plain,
    ( v1_finset_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55,c_5,c_4,c_104])).

cnf(c_3,negated_conjecture,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_396,c_360,c_357,c_349,c_129,c_3,c_5])).


%------------------------------------------------------------------------------
