%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0906+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 27.83s
% Output     : CNFRefutation 27.83s
% Verified   : 
% Statistics : Number of formulae       :   46 (  90 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 264 expanded)
%              Number of equality atoms :  109 ( 219 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1373,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1374,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f1373])).

fof(f2765,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1374])).

fof(f3820,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
     => ( ( k2_mcart_1(sK416) = sK416
          | k1_mcart_1(sK416) = sK416 )
        & m1_subset_1(sK416,k2_zfmisc_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3819,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1) )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK414,sK415)) )
      & k1_xboole_0 != k2_zfmisc_1(sK414,sK415) ) ),
    introduced(choice_axiom,[])).

fof(f3821,plain,
    ( ( k2_mcart_1(sK416) = sK416
      | k1_mcart_1(sK416) = sK416 )
    & m1_subset_1(sK416,k2_zfmisc_1(sK414,sK415))
    & k1_xboole_0 != k2_zfmisc_1(sK414,sK415) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK414,sK415,sK416])],[f2765,f3820,f3819])).

fof(f6254,plain,(
    m1_subset_1(sK416,k2_zfmisc_1(sK414,sK415)) ),
    inference(cnf_transformation,[],[f3821])).

fof(f6255,plain,
    ( k2_mcart_1(sK416) = sK416
    | k1_mcart_1(sK416) = sK416 ),
    inference(cnf_transformation,[],[f3821])).

fof(f1331,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2731,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1331])).

fof(f6156,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2731])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3833,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7012,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6156,f3833,f3833])).

fof(f6155,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2731])).

fof(f7013,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6155,f3833,f3833])).

fof(f6253,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK414,sK415) ),
    inference(cnf_transformation,[],[f3821])).

fof(f7110,plain,(
    o_0_0_xboole_0 != k2_zfmisc_1(sK414,sK415) ),
    inference(definition_unfolding,[],[f6253,f3833])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2955,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f2956,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2955])).

fof(f4290,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2956])).

fof(f6551,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f4290,f3833,f3833])).

fof(f7184,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f6551])).

fof(f4289,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2956])).

fof(f6552,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f4289,f3833,f3833])).

fof(f7185,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f6552])).

cnf(c_2409,negated_conjecture,
    ( m1_subset_1(sK416,k2_zfmisc_1(sK414,sK415)) ),
    inference(cnf_transformation,[],[f6254])).

cnf(c_68341,plain,
    ( m1_subset_1(sK416,k2_zfmisc_1(sK414,sK415)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_2408,negated_conjecture,
    ( k2_mcart_1(sK416) = sK416
    | k1_mcart_1(sK416) = sK416 ),
    inference(cnf_transformation,[],[f6255])).

cnf(c_2310,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k2_mcart_1(X0) != X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f7012])).

cnf(c_68394,plain,
    ( k2_mcart_1(X0) != X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2310])).

cnf(c_88540,plain,
    ( k1_mcart_1(sK416) = sK416
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK416,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_68394])).

cnf(c_2311,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k1_mcart_1(X0) != X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f7013])).

cnf(c_68393,plain,
    ( k1_mcart_1(X0) != X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2311])).

cnf(c_88597,plain,
    ( o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK416,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_88540,c_68393])).

cnf(c_88599,plain,
    ( sK415 = o_0_0_xboole_0
    | sK414 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_68341,c_88597])).

cnf(c_2410,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK414,sK415) ),
    inference(cnf_transformation,[],[f7110])).

cnf(c_88609,plain,
    ( k2_zfmisc_1(sK414,o_0_0_xboole_0) != o_0_0_xboole_0
    | sK414 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_88599,c_2410])).

cnf(c_450,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7184])).

cnf(c_88612,plain,
    ( sK414 = o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88609,c_450])).

cnf(c_88613,plain,
    ( sK414 = o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_88612])).

cnf(c_88631,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK415) != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88613,c_2410])).

cnf(c_451,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7185])).

cnf(c_88633,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_88631,c_451])).

cnf(c_88634,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_88633])).

%------------------------------------------------------------------------------
