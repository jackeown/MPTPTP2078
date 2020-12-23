%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1041+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 55.35s
% Output     : CNFRefutation 55.35s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 694 expanded)
%              Number of clauses        :   37 ( 171 expanded)
%              Number of leaves         :    7 ( 189 expanded)
%              Depth                    :   15
%              Number of atoms          :  251 (4007 expanded)
%              Number of equality atoms :  107 ( 510 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1544,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3215,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1544])).

fof(f3216,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3215])).

fof(f7628,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3216])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4701,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8871,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | o_0_0_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7628,f4701])).

fof(f9294,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(o_0_0_xboole_0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_2(X3,o_0_0_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f8871])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3563,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f3564,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f3563])).

fof(f5157,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f3564])).

fof(f8084,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f5157,f4701,f4701])).

fof(f9012,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f8084])).

fof(f376,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5236,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f8132,plain,(
    k1_tarski(o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f5236,f4701,f4701])).

fof(f1545,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_hidden(X2,k5_partfun1(X0,X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1546,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_hidden(X2,k5_partfun1(X0,X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1545])).

fof(f3217,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1546])).

fof(f3218,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f3217])).

fof(f4647,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_hidden(sK551,k5_partfun1(X0,X0,X1))
        & r1_partfun1(X1,sK551)
        & m1_subset_1(sK551,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK551,X0,X0)
        & v1_funct_1(sK551) ) ) ),
    introduced(choice_axiom,[])).

fof(f4646,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(sK549,sK549,sK550))
          & r1_partfun1(sK550,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549)))
          & v1_funct_2(X2,sK549,sK549)
          & v1_funct_1(X2) )
      & m1_subset_1(sK550,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549)))
      & v1_funct_1(sK550) ) ),
    introduced(choice_axiom,[])).

fof(f4648,plain,
    ( ~ r2_hidden(sK551,k5_partfun1(sK549,sK549,sK550))
    & r1_partfun1(sK550,sK551)
    & m1_subset_1(sK551,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549)))
    & v1_funct_2(sK551,sK549,sK549)
    & v1_funct_1(sK551)
    & m1_subset_1(sK550,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549)))
    & v1_funct_1(sK550) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK549,sK550,sK551])],[f3218,f4647,f4646])).

fof(f7633,plain,(
    m1_subset_1(sK551,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) ),
    inference(cnf_transformation,[],[f4648])).

fof(f7627,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3216])).

fof(f8872,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | o_0_0_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7627,f4701])).

fof(f7631,plain,(
    v1_funct_1(sK551) ),
    inference(cnf_transformation,[],[f4648])).

fof(f7632,plain,(
    v1_funct_2(sK551,sK549,sK549) ),
    inference(cnf_transformation,[],[f4648])).

fof(f7629,plain,(
    v1_funct_1(sK550) ),
    inference(cnf_transformation,[],[f4648])).

fof(f7634,plain,(
    r1_partfun1(sK550,sK551) ),
    inference(cnf_transformation,[],[f4648])).

fof(f7635,plain,(
    ~ r2_hidden(sK551,k5_partfun1(sK549,sK549,sK550)) ),
    inference(cnf_transformation,[],[f4648])).

fof(f7630,plain,(
    m1_subset_1(sK550,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) ),
    inference(cnf_transformation,[],[f4648])).

cnf(c_2909,plain,
    ( ~ v1_funct_2(X0,o_0_0_xboole_0,X1)
    | ~ r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | r2_hidden(X0,k5_partfun1(o_0_0_xboole_0,X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f9294])).

cnf(c_88684,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | r2_hidden(X0,k5_partfun1(o_0_0_xboole_0,X1,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2909])).

cnf(c_451,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f9012])).

cnf(c_530,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8132])).

cnf(c_106748,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(X2,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | r2_hidden(X0,k5_partfun1(o_0_0_xboole_0,X1,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_88684,c_451,c_530])).

cnf(c_2913,negated_conjecture,
    ( m1_subset_1(sK551,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) ),
    inference(cnf_transformation,[],[f7633])).

cnf(c_88680,plain,
    ( m1_subset_1(sK551,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2913])).

cnf(c_2910,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f8872])).

cnf(c_88683,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_partfun1(X3,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k5_partfun1(X2,X0,X3)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2910])).

cnf(c_121778,plain,
    ( sK549 = o_0_0_xboole_0
    | v1_funct_2(sK551,sK549,sK549) != iProver_top
    | r1_partfun1(X0,sK551) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) != iProver_top
    | r2_hidden(sK551,k5_partfun1(sK549,sK549,X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK551) != iProver_top ),
    inference(superposition,[status(thm)],[c_88680,c_88683])).

cnf(c_2915,negated_conjecture,
    ( v1_funct_1(sK551) ),
    inference(cnf_transformation,[],[f7631])).

cnf(c_3080,plain,
    ( v1_funct_1(sK551) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2915])).

cnf(c_2914,negated_conjecture,
    ( v1_funct_2(sK551,sK549,sK549) ),
    inference(cnf_transformation,[],[f7632])).

cnf(c_3081,plain,
    ( v1_funct_2(sK551,sK549,sK549) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_122769,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK551,k5_partfun1(sK549,sK549,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) != iProver_top
    | r1_partfun1(X0,sK551) != iProver_top
    | sK549 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_121778,c_3080,c_3081])).

cnf(c_122770,plain,
    ( sK549 = o_0_0_xboole_0
    | r1_partfun1(X0,sK551) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) != iProver_top
    | r2_hidden(sK551,k5_partfun1(sK549,sK549,X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_122769])).

cnf(c_122780,plain,
    ( sK549 = o_0_0_xboole_0
    | r1_partfun1(sK551,sK551) != iProver_top
    | r2_hidden(sK551,k5_partfun1(sK549,sK549,sK551)) = iProver_top
    | v1_funct_1(sK551) != iProver_top ),
    inference(superposition,[status(thm)],[c_88680,c_122770])).

cnf(c_2917,negated_conjecture,
    ( v1_funct_1(sK550) ),
    inference(cnf_transformation,[],[f7629])).

cnf(c_3078,plain,
    ( v1_funct_1(sK550) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2917])).

cnf(c_2912,negated_conjecture,
    ( r1_partfun1(sK550,sK551) ),
    inference(cnf_transformation,[],[f7634])).

cnf(c_3083,plain,
    ( r1_partfun1(sK550,sK551) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2912])).

cnf(c_2911,negated_conjecture,
    ( ~ r2_hidden(sK551,k5_partfun1(sK549,sK549,sK550)) ),
    inference(cnf_transformation,[],[f7635])).

cnf(c_3084,plain,
    ( r2_hidden(sK551,k5_partfun1(sK549,sK549,sK550)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2911])).

cnf(c_2916,negated_conjecture,
    ( m1_subset_1(sK550,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) ),
    inference(cnf_transformation,[],[f7630])).

cnf(c_88677,plain,
    ( m1_subset_1(sK550,k1_zfmisc_1(k2_zfmisc_1(sK549,sK549))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2916])).

cnf(c_122781,plain,
    ( sK549 = o_0_0_xboole_0
    | r1_partfun1(sK550,sK551) != iProver_top
    | r2_hidden(sK551,k5_partfun1(sK549,sK549,sK550)) = iProver_top
    | v1_funct_1(sK550) != iProver_top ),
    inference(superposition,[status(thm)],[c_88677,c_122770])).

cnf(c_122801,plain,
    ( sK549 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_122780,c_3078,c_3083,c_3084,c_122781])).

cnf(c_88682,plain,
    ( r2_hidden(sK551,k5_partfun1(sK549,sK549,sK550)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2911])).

cnf(c_122812,plain,
    ( r2_hidden(sK551,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK550)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_122801,c_88682])).

cnf(c_204946,plain,
    ( v1_funct_2(sK551,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK550,sK551) != iProver_top
    | m1_subset_1(sK550,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(sK551,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(sK550) != iProver_top
    | v1_funct_1(sK551) != iProver_top ),
    inference(superposition,[status(thm)],[c_106748,c_122812])).

cnf(c_122813,plain,
    ( m1_subset_1(sK551,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_122801,c_88680])).

cnf(c_122822,plain,
    ( m1_subset_1(sK551,k1_tarski(o_0_0_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_122813,c_451,c_530])).

cnf(c_122814,plain,
    ( m1_subset_1(sK550,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_122801,c_88677])).

cnf(c_122819,plain,
    ( m1_subset_1(sK550,k1_tarski(o_0_0_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_122814,c_451,c_530])).

cnf(c_88679,plain,
    ( v1_funct_2(sK551,sK549,sK549) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_122815,plain,
    ( v1_funct_2(sK551,o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_122801,c_88679])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_204946,c_122822,c_122819,c_122815,c_3083,c_3080,c_3078])).

%------------------------------------------------------------------------------
