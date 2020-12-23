%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1294+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:22 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of clauses        :   35 (  39 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 254 expanded)
%              Number of equality atoms :   98 ( 185 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k7_setfam_1(X0,X1) != k1_xboole_0 )
        & ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k7_setfam_1(X0,X1) != k1_xboole_0 )
          & ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k7_setfam_1(X0,X1) != k1_xboole_0 )
        | ( k7_setfam_1(X0,X1) = k1_xboole_0
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k7_setfam_1(X0,X1) != k1_xboole_0 )
          | ( k7_setfam_1(X0,X1) = k1_xboole_0
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ( k1_xboole_0 = sK1
          & k7_setfam_1(sK0,sK1) != k1_xboole_0 )
        | ( k7_setfam_1(sK0,sK1) = k1_xboole_0
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ( ( k1_xboole_0 = sK1
        & k7_setfam_1(sK0,sK1) != k1_xboole_0 )
      | ( k7_setfam_1(sK0,sK1) = k1_xboole_0
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f17,plain,
    ( k7_setfam_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,
    ( k1_xboole_0 = sK1
    | k7_setfam_1(sK0,sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_127,plain,
    ( X0_34 != X1_34
    | k7_setfam_1(X0_35,X0_34) = k7_setfam_1(X0_35,X1_34) ),
    theory(equality)).

cnf(c_400,plain,
    ( X0_34 != sK1
    | k7_setfam_1(sK0,X0_34) = k7_setfam_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_402,plain,
    ( k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_126,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_348,plain,
    ( X0_34 != X1_34
    | k7_setfam_1(sK0,sK1) != X1_34
    | k7_setfam_1(sK0,sK1) = X0_34 ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_384,plain,
    ( X0_34 != k7_setfam_1(sK0,sK1)
    | k7_setfam_1(sK0,sK1) = X0_34
    | k7_setfam_1(sK0,sK1) != k7_setfam_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_399,plain,
    ( k7_setfam_1(sK0,X0_34) != k7_setfam_1(sK0,sK1)
    | k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,X0_34)
    | k7_setfam_1(sK0,sK1) != k7_setfam_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_401,plain,
    ( k7_setfam_1(sK0,sK1) != k7_setfam_1(sK0,sK1)
    | k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,k1_xboole_0)
    | k7_setfam_1(sK0,k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_121,plain,
    ( ~ m1_subset_1(X0_34,k1_zfmisc_1(k1_zfmisc_1(X0_35)))
    | k7_setfam_1(X0_35,X0_34) != k1_xboole_0
    | k1_xboole_0 = X0_34 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_367,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,X0_34),k1_zfmisc_1(k1_zfmisc_1(X0_35)))
    | k7_setfam_1(X0_35,k7_setfam_1(sK0,X0_34)) != k1_xboole_0
    | k1_xboole_0 = k7_setfam_1(sK0,X0_34) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_369,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_332,plain,
    ( k7_setfam_1(sK0,sK1) != X0_34
    | k7_setfam_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0_34 ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_349,plain,
    ( k7_setfam_1(sK0,sK1) != k7_setfam_1(sK0,X0_34)
    | k7_setfam_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k7_setfam_1(sK0,X0_34) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_351,plain,
    ( k7_setfam_1(sK0,sK1) != k7_setfam_1(sK0,k1_xboole_0)
    | k7_setfam_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_125,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_347,plain,
    ( k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_6,negated_conjecture,
    ( k7_setfam_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_119,negated_conjecture,
    ( k7_setfam_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_296,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X0_35)))
    | k7_setfam_1(X0_35,sK1) != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_298,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k7_setfam_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_314,negated_conjecture,
    ( k7_setfam_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_119,c_7,c_298])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0_34,X0_35)
    | m1_subset_1(X1_34,X0_35)
    | X1_34 != X0_34 ),
    theory(equality)).

cnf(c_309,plain,
    ( m1_subset_1(X0_34,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | X0_34 != sK1 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_311,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_3,negated_conjecture,
    ( k7_setfam_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_120,negated_conjecture,
    ( k7_setfam_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_122,plain,
    ( ~ m1_subset_1(X0_34,k1_zfmisc_1(k1_zfmisc_1(X0_35)))
    | k7_setfam_1(X0_35,k7_setfam_1(X0_35,X0_34)) = X0_34 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_137,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_123,plain,
    ( ~ m1_subset_1(X0_34,k1_zfmisc_1(k1_zfmisc_1(X0_35)))
    | m1_subset_1(k7_setfam_1(X0_35,X0_34),k1_zfmisc_1(k1_zfmisc_1(X0_35))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_134,plain,
    ( m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_402,c_401,c_369,c_351,c_347,c_314,c_311,c_120,c_137,c_134,c_7])).


%------------------------------------------------------------------------------
