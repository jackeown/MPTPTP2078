%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1844+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:38 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 179 expanded)
%              Number of clauses        :   34 (  49 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  224 ( 698 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),u1_struct_0(X0))
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v7_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v7_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,X0)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_xboole_0(X1)
           => v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_150,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_151,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_11,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_153,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_151,c_13,c_11,c_29])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_153])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0_41,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_41),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_247])).

cnf(c_375,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_153])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0_41,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0_41) = k1_tarski(X0_41) ),
    inference(subtyping,[status(esa)],[c_235])).

cnf(c_372,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_6,plain,
    ( v1_zfmisc_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_79,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_1])).

cnf(c_80,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_79])).

cnf(c_9,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(u1_struct_0(sK0),sK1) != X0
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_80,c_9])).

cnf(c_177,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_zfmisc_1(k6_domain_1(u1_struct_0(sK0),sK1))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_12,negated_conjecture,
    ( ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_23,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_179,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_zfmisc_1(k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_177,c_13,c_12,c_11,c_23,c_29])).

cnf(c_219,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(X0) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_179])).

cnf(c_352,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(X0_41) ),
    inference(subtyping,[status(esa)],[c_219])).

cnf(c_369,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_375,c_372,c_369,c_10])).


%------------------------------------------------------------------------------
