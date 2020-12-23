%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0908+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 35.70s
% Output     : CNFRefutation 35.70s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 221 expanded)
%              Number of clauses        :   27 (  36 expanded)
%              Number of leaves         :    7 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  239 (1110 expanded)
%              Number of equality atoms :  214 ( 991 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1375,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1376,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
       => ~ ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f1375])).

fof(f2769,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1376])).

fof(f2770,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f2769])).

fof(f3825,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
     => ( ( k7_mcart_1(X0,X1,X2,X3) != sK420
          | k6_mcart_1(X0,X1,X2,X3) != sK419
          | k5_mcart_1(X0,X1,X2,X3) != sK418 )
        & k3_mcart_1(sK418,sK419,sK420) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f3824,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4,X5,X6] :
            ( ( k7_mcart_1(X0,X1,X2,X3) != X6
              | k6_mcart_1(X0,X1,X2,X3) != X5
              | k5_mcart_1(X0,X1,X2,X3) != X4 )
            & k3_mcart_1(X4,X5,X6) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
   => ( ? [X6,X5,X4] :
          ( ( k7_mcart_1(sK414,sK415,sK416,sK417) != X6
            | k6_mcart_1(sK414,sK415,sK416,sK417) != X5
            | k5_mcart_1(sK414,sK415,sK416,sK417) != X4 )
          & k3_mcart_1(X4,X5,X6) = sK417 )
      & k1_xboole_0 != sK416
      & k1_xboole_0 != sK415
      & k1_xboole_0 != sK414
      & m1_subset_1(sK417,k3_zfmisc_1(sK414,sK415,sK416)) ) ),
    introduced(choice_axiom,[])).

fof(f3826,plain,
    ( ( k7_mcart_1(sK414,sK415,sK416,sK417) != sK420
      | k6_mcart_1(sK414,sK415,sK416,sK417) != sK419
      | k5_mcart_1(sK414,sK415,sK416,sK417) != sK418 )
    & k3_mcart_1(sK418,sK419,sK420) = sK417
    & k1_xboole_0 != sK416
    & k1_xboole_0 != sK415
    & k1_xboole_0 != sK414
    & m1_subset_1(sK417,k3_zfmisc_1(sK414,sK415,sK416)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK414,sK415,sK416,sK417,sK418,sK419,sK420])],[f2770,f3825,f3824])).

fof(f6262,plain,(
    m1_subset_1(sK417,k3_zfmisc_1(sK414,sK415,sK416)) ),
    inference(cnf_transformation,[],[f3826])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6034,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f7128,plain,(
    m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416)) ),
    inference(definition_unfolding,[],[f6262,f6034])).

fof(f6266,plain,(
    k3_mcart_1(sK418,sK419,sK420) = sK417 ),
    inference(cnf_transformation,[],[f3826])).

fof(f1276,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6033,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1276])).

fof(f7124,plain,(
    k4_tarski(k4_tarski(sK418,sK419),sK420) = sK417 ),
    inference(definition_unfolding,[],[f6266,f6033])).

fof(f1352,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2746,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X6
                & k6_mcart_1(X0,X1,X2,X3) = X5
                & k5_mcart_1(X0,X1,X2,X3) = X4 )
              | k3_mcart_1(X4,X5,X6) != X3 )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1352])).

fof(f6202,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2746])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3838,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7064,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6202,f6033,f6034,f3838,f3838,f3838])).

fof(f7411,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X6
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7064])).

fof(f6267,plain,
    ( k7_mcart_1(sK414,sK415,sK416,sK417) != sK420
    | k6_mcart_1(sK414,sK415,sK416,sK417) != sK419
    | k5_mcart_1(sK414,sK415,sK416,sK417) != sK418 ),
    inference(cnf_transformation,[],[f3826])).

fof(f6200,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2746])).

fof(f7066,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6200,f6033,f6034,f3838,f3838,f3838])).

fof(f7413,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X4
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7066])).

fof(f6201,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2746])).

fof(f7065,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6201,f6033,f6034,f3838,f3838,f3838])).

fof(f7412,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7065])).

fof(f6265,plain,(
    k1_xboole_0 != sK416 ),
    inference(cnf_transformation,[],[f3826])).

fof(f7125,plain,(
    o_0_0_xboole_0 != sK416 ),
    inference(definition_unfolding,[],[f6265,f3838])).

fof(f6264,plain,(
    k1_xboole_0 != sK415 ),
    inference(cnf_transformation,[],[f3826])).

fof(f7126,plain,(
    o_0_0_xboole_0 != sK415 ),
    inference(definition_unfolding,[],[f6264,f3838])).

fof(f6263,plain,(
    k1_xboole_0 != sK414 ),
    inference(cnf_transformation,[],[f3826])).

fof(f7127,plain,(
    o_0_0_xboole_0 != sK414 ),
    inference(definition_unfolding,[],[f6263,f3838])).

cnf(c_2417,negated_conjecture,
    ( m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416)) ),
    inference(cnf_transformation,[],[f7128])).

cnf(c_107875,plain,
    ( m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_2413,negated_conjecture,
    ( k4_tarski(k4_tarski(sK418,sK419),sK420) = sK417 ),
    inference(cnf_transformation,[],[f7124])).

cnf(c_2350,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
    | k7_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X2
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f7411])).

cnf(c_107920,plain,
    ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2350])).

cnf(c_128209,plain,
    ( k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK418,sK419),sK420)) = sK420
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_107920])).

cnf(c_128227,plain,
    ( k7_mcart_1(X0,X1,X2,sK417) = sK420
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_128209,c_2413])).

cnf(c_128437,plain,
    ( k7_mcart_1(sK414,sK415,sK416,sK417) = sK420
    | sK416 = o_0_0_xboole_0
    | sK415 = o_0_0_xboole_0
    | sK414 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_107875,c_128227])).

cnf(c_2412,negated_conjecture,
    ( k7_mcart_1(sK414,sK415,sK416,sK417) != sK420
    | k6_mcart_1(sK414,sK415,sK416,sK417) != sK419
    | k5_mcart_1(sK414,sK415,sK416,sK417) != sK418 ),
    inference(cnf_transformation,[],[f6267])).

cnf(c_2352,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
    | k5_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X0
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f7413])).

cnf(c_107918,plain,
    ( k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X3
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2352])).

cnf(c_127807,plain,
    ( k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK418,sK419),sK420)) = sK418
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_107918])).

cnf(c_127825,plain,
    ( k5_mcart_1(X0,X1,X2,sK417) = sK418
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_127807,c_2413])).

cnf(c_127852,plain,
    ( k5_mcart_1(sK414,sK415,sK416,sK417) = sK418
    | sK416 = o_0_0_xboole_0
    | sK415 = o_0_0_xboole_0
    | sK414 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_107875,c_127825])).

cnf(c_2351,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
    | k6_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X1
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f7412])).

cnf(c_107919,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2351])).

cnf(c_127944,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK418,sK419),sK420)) = sK419
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_107919])).

cnf(c_127962,plain,
    ( k6_mcart_1(X0,X1,X2,sK417) = sK419
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | m1_subset_1(sK417,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_127944,c_2413])).

cnf(c_128052,plain,
    ( k6_mcart_1(sK414,sK415,sK416,sK417) = sK419
    | sK416 = o_0_0_xboole_0
    | sK415 = o_0_0_xboole_0
    | sK414 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_107875,c_127962])).

cnf(c_128466,plain,
    ( sK416 = o_0_0_xboole_0
    | sK415 = o_0_0_xboole_0
    | sK414 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_128437,c_2412,c_127852,c_128052])).

cnf(c_2414,negated_conjecture,
    ( o_0_0_xboole_0 != sK416 ),
    inference(cnf_transformation,[],[f7125])).

cnf(c_128475,plain,
    ( sK415 = o_0_0_xboole_0
    | sK414 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_128466,c_2414])).

cnf(c_2415,negated_conjecture,
    ( o_0_0_xboole_0 != sK415 ),
    inference(cnf_transformation,[],[f7126])).

cnf(c_128490,plain,
    ( sK414 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_128475,c_2415])).

cnf(c_2416,negated_conjecture,
    ( o_0_0_xboole_0 != sK414 ),
    inference(cnf_transformation,[],[f7127])).

cnf(c_128500,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_128490,c_2416])).

cnf(c_128501,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_128500])).

%------------------------------------------------------------------------------
