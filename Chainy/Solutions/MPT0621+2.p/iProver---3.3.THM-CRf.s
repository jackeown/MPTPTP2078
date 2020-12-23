%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0621+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 22.89s
% Output     : CNFRefutation 22.89s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 813 expanded)
%              Number of clauses        :   59 ( 228 expanded)
%              Number of leaves         :   16 ( 220 expanded)
%              Depth                    :   22
%              Number of atoms          :  364 (3415 expanded)
%              Number of equality atoms :  253 (2037 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f896,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1645,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f2148,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK172(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK172(X0)) = X0
        & v1_funct_1(sK172(X0))
        & v1_relat_1(sK172(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2149,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK172(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK172(X0)) = X0
      & v1_funct_1(sK172(X0))
      & v1_relat_1(sK172(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK172])],[f1645,f2148])).

fof(f3531,plain,(
    ! [X0] : k1_relat_1(sK172(X0)) = X0 ),
    inference(cnf_transformation,[],[f2149])).

fof(f901,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1651,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f901])).

fof(f2152,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK174(X0,X1))
        & k1_relat_1(sK174(X0,X1)) = X0
        & v1_funct_1(sK174(X0,X1))
        & v1_relat_1(sK174(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2153,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK174(X0,X1))
          & k1_relat_1(sK174(X0,X1)) = X0
          & v1_funct_1(sK174(X0,X1))
          & v1_relat_1(sK174(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK174])],[f1651,f2152])).

fof(f3542,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK174(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2153])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2167,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4144,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK174(X0,X1)) = X0
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f3542,f2167])).

fof(f902,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f903,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f902])).

fof(f1652,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f903])).

fof(f1653,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f1652])).

fof(f2154,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK175
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK175
              | k1_relat_1(X1) != sK175
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f2155,plain,
    ( k1_xboole_0 != sK175
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK175
            | k1_relat_1(X1) != sK175
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK175])],[f1653,f2154])).

fof(f3544,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK175
      | k1_relat_1(X1) != sK175
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2155])).

fof(f3545,plain,(
    k1_xboole_0 != sK175 ),
    inference(cnf_transformation,[],[f2155])).

fof(f4147,plain,(
    o_0_0_xboole_0 != sK175 ),
    inference(definition_unfolding,[],[f3545,f2167])).

fof(f3540,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK174(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2153])).

fof(f4146,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK174(X0,X1))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f3540,f2167])).

fof(f3541,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK174(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2153])).

fof(f4145,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK174(X0,X1))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f3541,f2167])).

fof(f3529,plain,(
    ! [X0] : v1_relat_1(sK172(X0)) ),
    inference(cnf_transformation,[],[f2149])).

fof(f3530,plain,(
    ! [X0] : v1_funct_1(sK172(X0)) ),
    inference(cnf_transformation,[],[f2149])).

fof(f3543,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK174(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2153])).

fof(f4143,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK174(X0,X1))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f3543,f2167])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1288,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f3111,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1288])).

fof(f4031,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f3111,f2167,f2167])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3110,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f4030,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f3110,f2167])).

fof(f827,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1565,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f827])).

fof(f1566,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1565])).

fof(f3430,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1566])).

fof(f4336,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f3430])).

fof(f695,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3276,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f695])).

fof(f897,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1646,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f897])).

fof(f2150,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK173(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK173(X0)) = X0
        & v1_funct_1(sK173(X0))
        & v1_relat_1(sK173(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2151,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK173(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK173(X0)) = X0
      & v1_funct_1(sK173(X0))
      & v1_relat_1(sK173(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK173])],[f1646,f2150])).

fof(f3535,plain,(
    ! [X0] : k1_relat_1(sK173(X0)) = X0 ),
    inference(cnf_transformation,[],[f2151])).

fof(f3533,plain,(
    ! [X0] : v1_relat_1(sK173(X0)) ),
    inference(cnf_transformation,[],[f2151])).

fof(f3534,plain,(
    ! [X0] : v1_funct_1(sK173(X0)) ),
    inference(cnf_transformation,[],[f2151])).

fof(f389,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2715,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f389])).

fof(f347,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1070,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f347])).

fof(f2653,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1070])).

fof(f3851,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f2653,f2167,f2167])).

cnf(c_1356,plain,
    ( k1_relat_1(sK172(X0)) = X0 ),
    inference(cnf_transformation,[],[f3531])).

cnf(c_1367,plain,
    ( k1_relat_1(sK174(X0,X1)) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f4144])).

cnf(c_1371,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_relat_1(X1) != sK175
    | k1_relat_1(X0) != sK175 ),
    inference(cnf_transformation,[],[f3544])).

cnf(c_55275,plain,
    ( X0 = X1
    | k1_relat_1(X1) != sK175
    | k1_relat_1(X0) != sK175
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_68063,plain,
    ( sK174(X0,X1) = X2
    | k1_relat_1(X2) != sK175
    | sK175 != X0
    | o_0_0_xboole_0 = X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK174(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK174(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_55275])).

cnf(c_1370,negated_conjecture,
    ( o_0_0_xboole_0 != sK175 ),
    inference(cnf_transformation,[],[f4147])).

cnf(c_1369,plain,
    ( v1_relat_1(sK174(X0,X1))
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f4146])).

cnf(c_1395,plain,
    ( o_0_0_xboole_0 = X0
    | v1_relat_1(sK174(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_1368,plain,
    ( v1_funct_1(sK174(X0,X1))
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f4145])).

cnf(c_1398,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_1(sK174(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_35480,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_68262,plain,
    ( sK175 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK175 ),
    inference(instantiation,[status(thm)],[c_35480])).

cnf(c_68292,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK175 != X0
    | k1_relat_1(X2) != sK175
    | sK174(X0,X1) = X2
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68063,c_1370,c_1395,c_1398,c_68262])).

cnf(c_68293,plain,
    ( sK174(X0,X1) = X2
    | k1_relat_1(X2) != sK175
    | sK175 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_68292])).

cnf(c_68307,plain,
    ( sK174(X0,X1) = sK172(X2)
    | sK175 != X2
    | sK175 != X0
    | v1_funct_1(sK172(X2)) != iProver_top
    | v1_relat_1(sK172(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_68293])).

cnf(c_66184,plain,
    ( sK172(X0) = X1
    | k1_relat_1(X1) != sK175
    | sK175 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK172(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK172(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_55275])).

cnf(c_1358,plain,
    ( v1_relat_1(sK172(X0)) ),
    inference(cnf_transformation,[],[f3529])).

cnf(c_1420,plain,
    ( v1_relat_1(sK172(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_1357,plain,
    ( v1_funct_1(sK172(X0)) ),
    inference(cnf_transformation,[],[f3530])).

cnf(c_1423,plain,
    ( v1_funct_1(sK172(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1357])).

cnf(c_66608,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK172(X0) = X1
    | k1_relat_1(X1) != sK175
    | sK175 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_66184,c_1420,c_1423])).

cnf(c_66609,plain,
    ( sK172(X0) = X1
    | k1_relat_1(X1) != sK175
    | sK175 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_66608])).

cnf(c_68061,plain,
    ( sK174(X0,X1) = sK172(X2)
    | sK175 != X0
    | sK175 != X2
    | o_0_0_xboole_0 = X0
    | v1_funct_1(sK174(X0,X1)) != iProver_top
    | v1_relat_1(sK174(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_66609])).

cnf(c_68502,plain,
    ( sK174(X0,X1) = sK172(X2)
    | sK175 != X2
    | sK175 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_68307,c_1370,c_1395,c_1398,c_68061,c_68262])).

cnf(c_68503,plain,
    ( sK174(X0,X1) = sK172(X2)
    | sK175 != X0
    | sK175 != X2 ),
    inference(renaming,[status(thm)],[c_68502])).

cnf(c_68507,plain,
    ( sK174(sK175,X0) = sK172(X1)
    | sK175 != X1 ),
    inference(equality_resolution,[status(thm)],[c_68503])).

cnf(c_69868,plain,
    ( sK174(sK175,X0) = sK172(sK175) ),
    inference(equality_resolution,[status(thm)],[c_68507])).

cnf(c_1366,plain,
    ( k2_relat_1(sK174(X0,X1)) = k1_tarski(X1)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f4143])).

cnf(c_74053,plain,
    ( k2_relat_1(sK172(sK175)) = k1_tarski(X0)
    | sK175 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_69868,c_1366])).

cnf(c_937,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f4031])).

cnf(c_2476,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_936,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4030])).

cnf(c_2479,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_68263,plain,
    ( sK175 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK175
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_68262])).

cnf(c_75502,plain,
    ( k2_relat_1(sK172(sK175)) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_74053,c_1370,c_2476,c_2479,c_68263])).

cnf(c_1257,plain,
    ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
    | k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4336])).

cnf(c_1102,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f3276])).

cnf(c_6594,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1257,c_1102])).

cnf(c_1360,plain,
    ( k1_relat_1(sK173(X0)) = X0 ),
    inference(cnf_transformation,[],[f3535])).

cnf(c_66348,plain,
    ( sK173(X0) = X1
    | k1_relat_1(X1) != sK175
    | sK175 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK173(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK173(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_55275])).

cnf(c_1362,plain,
    ( v1_relat_1(sK173(X0)) ),
    inference(cnf_transformation,[],[f3533])).

cnf(c_1410,plain,
    ( v1_relat_1(sK173(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1362])).

cnf(c_1361,plain,
    ( v1_funct_1(sK173(X0)) ),
    inference(cnf_transformation,[],[f3534])).

cnf(c_1413,plain,
    ( v1_funct_1(sK173(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_66704,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK173(X0) = X1
    | k1_relat_1(X1) != sK175
    | sK175 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_66348,c_1410,c_1413])).

cnf(c_66705,plain,
    ( sK173(X0) = X1
    | k1_relat_1(X1) != sK175
    | sK175 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_66704])).

cnf(c_66715,plain,
    ( k1_tarski(X0) != sK175
    | k1_tarski(k4_tarski(X0,X1)) = sK173(X2)
    | sK175 != X2
    | v1_funct_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top
    | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6594,c_66705])).

cnf(c_2079,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_68997,plain,
    ( v1_funct_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top
    | sK175 != X2
    | k1_tarski(k4_tarski(X0,X1)) = sK173(X2)
    | k1_tarski(X0) != sK175 ),
    inference(global_propositional_subsumption,[status(thm)],[c_66715,c_2079])).

cnf(c_68998,plain,
    ( k1_tarski(X0) != sK175
    | k1_tarski(k4_tarski(X0,X1)) = sK173(X2)
    | sK175 != X2
    | v1_funct_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_68997])).

cnf(c_75511,plain,
    ( k2_relat_1(sK172(sK175)) = sK173(X0)
    | k1_tarski(X1) != sK175
    | sK175 != X0
    | v1_funct_1(k2_relat_1(sK172(sK175))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_75502,c_68998])).

cnf(c_543,plain,
    ( k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f2715])).

cnf(c_75643,plain,
    ( k3_tarski(k2_relat_1(sK172(sK175))) = X0 ),
    inference(superposition,[status(thm)],[c_75502,c_543])).

cnf(c_480,plain,
    ( k2_zfmisc_1(X0,k1_tarski(X1)) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3851])).

cnf(c_75647,plain,
    ( k2_zfmisc_1(X0,k2_relat_1(sK172(sK175))) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_75502,c_480])).

cnf(c_75669,plain,
    ( k3_tarski(k2_relat_1(sK172(sK175))) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_75643,c_75647])).

cnf(c_75673,plain,
    ( o_0_0_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_75669,c_75643])).

cnf(c_75920,plain,
    ( sK175 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_75511,c_1370,c_68262,c_75673])).

cnf(c_75923,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_75920])).

%------------------------------------------------------------------------------
