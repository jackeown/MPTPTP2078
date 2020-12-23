%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1843+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:38 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 181 expanded)
%              Number of clauses        :   38 (  52 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 ( 706 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ ( v7_struct_0(X0)
                & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( v7_struct_0(X0)
        & v1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),u1_struct_0(X0))
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v7_struct_0(X0)
            & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v7_struct_0(sK0)
          & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( v7_struct_0(sK0)
    & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f36,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_74,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_0,c_1])).

cnf(c_75,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_74])).

cnf(c_5,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_10,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_151,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_152,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_7,negated_conjecture,
    ( v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_21,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_154,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_152,c_10,c_7,c_21])).

cnf(c_164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_75,c_154])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_subset_1(X0,u1_struct_0(sK0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_164])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k6_domain_1(u1_struct_0(sK0),sK1) != X0
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_165])).

cnf(c_186,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_246,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(X0) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_186])).

cnf(c_340,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(X0_41) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_371,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_138,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_139,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_27,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_141,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_139,c_11,c_10,c_27])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_141])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0_41,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_41),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_235])).

cnf(c_368,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_141])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0_41,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0_41) = k1_tarski(X0_41) ),
    inference(subtyping,[status(esa)],[c_223])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_371,c_368,c_365,c_9])).


%------------------------------------------------------------------------------
