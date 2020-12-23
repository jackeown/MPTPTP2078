%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0899+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 27.92s
% Output     : CNFRefutation 27.92s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 475 expanded)
%              Number of clauses        :   56 (  72 expanded)
%              Number of leaves         :   23 ( 165 expanded)
%              Depth                    :   17
%              Number of atoms          :  770 (2321 expanded)
%              Number of equality atoms :  638 (2052 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1364,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1365,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ? [X4] :
              ( ? [X5,X6,X7,X8] :
                  ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                      & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                      & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                      & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                  & k4_mcart_1(X5,X6,X7,X8) = X4 )
              & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1364])).

fof(f2748,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1365])).

fof(f3799,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
     => ( ( k11_mcart_1(X0,X1,X2,X3,X4) != sK417
          | k10_mcart_1(X0,X1,X2,X3,X4) != sK416
          | k9_mcart_1(X0,X1,X2,X3,X4) != sK415
          | k8_mcart_1(X0,X1,X2,X3,X4) != sK414 )
        & k4_mcart_1(sK414,sK415,sK416,sK417) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f3798,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ? [X8,X7,X6,X5] :
            ( ( k11_mcart_1(X0,X1,X2,X3,sK413) != X8
              | k10_mcart_1(X0,X1,X2,X3,sK413) != X7
              | k9_mcart_1(X0,X1,X2,X3,sK413) != X6
              | k8_mcart_1(X0,X1,X2,X3,sK413) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = sK413 )
        & m1_subset_1(sK413,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3797,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( ? [X8,X7,X6,X5] :
              ( ( k11_mcart_1(sK409,sK410,sK411,sK412,X4) != X8
                | k10_mcart_1(sK409,sK410,sK411,sK412,X4) != X7
                | k9_mcart_1(sK409,sK410,sK411,sK412,X4) != X6
                | k8_mcart_1(sK409,sK410,sK411,sK412,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(sK409,sK410,sK411,sK412)) )
      & k1_xboole_0 != sK412
      & k1_xboole_0 != sK411
      & k1_xboole_0 != sK410
      & k1_xboole_0 != sK409 ) ),
    introduced(choice_axiom,[])).

fof(f3800,plain,
    ( ( k11_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK417
      | k10_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK416
      | k9_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK415
      | k8_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK414 )
    & k4_mcart_1(sK414,sK415,sK416,sK417) = sK413
    & m1_subset_1(sK413,k4_zfmisc_1(sK409,sK410,sK411,sK412))
    & k1_xboole_0 != sK412
    & k1_xboole_0 != sK411
    & k1_xboole_0 != sK410
    & k1_xboole_0 != sK409 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK409,sK410,sK411,sK412,sK413,sK414,sK415,sK416,sK417])],[f2748,f3799,f3798,f3797])).

fof(f6209,plain,(
    m1_subset_1(sK413,k4_zfmisc_1(sK409,sK410,sK411,sK412)) ),
    inference(cnf_transformation,[],[f3800])).

fof(f1279,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6012,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1279])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6010,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f6232,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6012,f6010])).

fof(f7040,plain,(
    m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK409,sK410),sK411),sK412)) ),
    inference(definition_unfolding,[],[f6209,f6232])).

fof(f6210,plain,(
    k4_mcart_1(sK414,sK415,sK416,sK417) = sK413 ),
    inference(cnf_transformation,[],[f3800])).

fof(f1278,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6011,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1276,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6009,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1276])).

fof(f6233,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6011,f6009])).

fof(f7039,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417) = sK413 ),
    inference(definition_unfolding,[],[f6210,f6233])).

fof(f1272,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X8 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2689,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1272])).

fof(f3661,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f2689])).

fof(f3662,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f3661])).

fof(f3663,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK338(X4,X5) != X5
        & k4_mcart_1(sK336(X4,X5),sK337(X4,X5),sK338(X4,X5),sK339(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f3664,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK338(X4,X5) != X5
                    & k4_mcart_1(sK336(X4,X5),sK337(X4,X5),sK338(X4,X5),sK339(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK336,sK337,sK338,sK339])],[f3662,f3663])).

fof(f5997,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3664])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3814,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6921,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f5997,f6233,f6232,f3814,f3814,f3814,f3814])).

fof(f7301,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f6921])).

fof(f7302,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) = X12
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)),X2)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7301])).

fof(f1285,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2698,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1285])).

fof(f6028,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f2698])).

fof(f6940,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f6028,f6232])).

fof(f1273,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X3)
                 => ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X9 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2690,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1273])).

fof(f3665,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f2690])).

fof(f3666,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f3665])).

fof(f3667,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X9
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK343(X4,X5) != X5
        & k4_mcart_1(sK340(X4,X5),sK341(X4,X5),sK342(X4,X5),sK343(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f3668,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK343(X4,X5) != X5
                    & k4_mcart_1(sK340(X4,X5),sK341(X4,X5),sK342(X4,X5),sK343(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK340,sK341,sK342,sK343])],[f3666,f3667])).

fof(f6000,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3668])).

fof(f6924,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6000,f6233,f6232,f3814,f3814,f3814,f3814])).

fof(f7303,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f6924])).

fof(f7304,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) = X13
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)),X3)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7303])).

fof(f1286,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2699,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1286])).

fof(f6029,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f2699])).

fof(f6941,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f6029,f6232])).

fof(f6211,plain,
    ( k11_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK417
    | k10_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK416
    | k9_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK415
    | k8_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK414 ),
    inference(cnf_transformation,[],[f3800])).

fof(f1284,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X7 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2697,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1284])).

fof(f3693,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f2697])).

fof(f3694,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f3693])).

fof(f3695,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X7
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK362(X4,X5) != X5
        & k4_mcart_1(sK361(X4,X5),sK362(X4,X5),sK363(X4,X5),sK364(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f3696,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK362(X4,X5) != X5
                    & k4_mcart_1(sK361(X4,X5),sK362(X4,X5),sK363(X4,X5),sK364(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK361,sK362,sK363,sK364])],[f3694,f3695])).

fof(f6025,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3696])).

fof(f6939,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6025,f6233,f6232,f3814,f3814,f3814,f3814])).

fof(f7321,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f6939])).

fof(f7322,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) = X11
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)),X1)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7321])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2704,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f6034,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f2704])).

fof(f6946,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f6034,f6232])).

fof(f1283,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X6 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2696,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1283])).

fof(f3689,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f2696])).

fof(f3690,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f3689])).

fof(f3691,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK357(X4,X5) != X5
        & k4_mcart_1(sK357(X4,X5),sK358(X4,X5),sK359(X4,X5),sK360(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f3692,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK357(X4,X5) != X5
                    & k4_mcart_1(sK357(X4,X5),sK358(X4,X5),sK359(X4,X5),sK360(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK357,sK358,sK359,sK360])],[f3690,f3691])).

fof(f6022,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3692])).

fof(f6936,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6022,f6233,f6232,f3814,f3814,f3814,f3814])).

fof(f7319,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f6936])).

fof(f7320,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)) = X10
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13)),X0)
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X10,X11),X12),X13),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f7319])).

fof(f1296,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2703,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1296])).

fof(f6033,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f2703])).

fof(f6945,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f6033,f6232])).

fof(f1360,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3795,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1360])).

fof(f3796,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f3795])).

fof(f6192,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f3796])).

fof(f7028,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f6192,f3814,f3814,f6232])).

fof(f7335,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f7028])).

fof(f6191,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3796])).

fof(f7029,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6191,f3814,f6232,f3814,f3814,f3814,f3814])).

fof(f6208,plain,(
    k1_xboole_0 != sK412 ),
    inference(cnf_transformation,[],[f3800])).

fof(f7041,plain,(
    o_0_0_xboole_0 != sK412 ),
    inference(definition_unfolding,[],[f6208,f3814])).

fof(f6207,plain,(
    k1_xboole_0 != sK411 ),
    inference(cnf_transformation,[],[f3800])).

fof(f7042,plain,(
    o_0_0_xboole_0 != sK411 ),
    inference(definition_unfolding,[],[f6207,f3814])).

fof(f6206,plain,(
    k1_xboole_0 != sK410 ),
    inference(cnf_transformation,[],[f3800])).

fof(f7043,plain,(
    o_0_0_xboole_0 != sK410 ),
    inference(definition_unfolding,[],[f6206,f3814])).

fof(f6205,plain,(
    k1_xboole_0 != sK409 ),
    inference(cnf_transformation,[],[f3800])).

fof(f7044,plain,(
    o_0_0_xboole_0 != sK409 ),
    inference(definition_unfolding,[],[f6205,f3814])).

cnf(c_2381,negated_conjecture,
    ( m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK409,sK410),sK411),sK412)) ),
    inference(cnf_transformation,[],[f7040])).

cnf(c_67573,plain,
    ( m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK409,sK410),sK411),sK412)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2381])).

cnf(c_2380,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417) = sK413 ),
    inference(cnf_transformation,[],[f7039])).

cnf(c_2177,plain,
    ( ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X2)
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
    | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f7302])).

cnf(c_67722,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X2) != iProver_top
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2177])).

cnf(c_2202,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) ),
    inference(cnf_transformation,[],[f6940])).

cnf(c_67703,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_82020,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_67722,c_67703])).

cnf(c_92444,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) = sK416
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_82020])).

cnf(c_92483,plain,
    ( k10_mcart_1(X0,X1,X2,X3,sK413) = sK416
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_92444,c_2380])).

cnf(c_92971,plain,
    ( k10_mcart_1(sK409,sK410,sK411,sK412,sK413) = sK416
    | sK412 = o_0_0_xboole_0
    | sK411 = o_0_0_xboole_0
    | sK410 = o_0_0_xboole_0
    | sK409 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_67573,c_92483])).

cnf(c_33546,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_92703,plain,
    ( sK409 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK409 ),
    inference(instantiation,[status(thm)],[c_33546])).

cnf(c_92704,plain,
    ( sK409 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK409
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_92703])).

cnf(c_92701,plain,
    ( sK410 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK410 ),
    inference(instantiation,[status(thm)],[c_33546])).

cnf(c_92702,plain,
    ( sK410 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK410
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_92701])).

cnf(c_92699,plain,
    ( sK411 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK411 ),
    inference(instantiation,[status(thm)],[c_33546])).

cnf(c_92700,plain,
    ( sK411 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK411
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_92699])).

cnf(c_92697,plain,
    ( sK412 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK412 ),
    inference(instantiation,[status(thm)],[c_33546])).

cnf(c_92698,plain,
    ( sK412 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK412
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_92697])).

cnf(c_2180,plain,
    ( ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X3)
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
    | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f7304])).

cnf(c_67719,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X3) != iProver_top
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2180])).

cnf(c_2203,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) ),
    inference(cnf_transformation,[],[f6941])).

cnf(c_67702,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2203])).

cnf(c_82006,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_67719,c_67702])).

cnf(c_91551,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) = sK417
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_82006])).

cnf(c_91590,plain,
    ( k11_mcart_1(X0,X1,X2,X3,sK413) = sK417
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91551,c_2380])).

cnf(c_91974,plain,
    ( k11_mcart_1(sK409,sK410,sK411,sK412,sK413) = sK417
    | sK412 = o_0_0_xboole_0
    | sK411 = o_0_0_xboole_0
    | sK410 = o_0_0_xboole_0
    | sK409 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_67573,c_91590])).

cnf(c_2379,negated_conjecture,
    ( k9_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK415
    | k8_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK414
    | k11_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK417
    | k10_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK416 ),
    inference(cnf_transformation,[],[f6211])).

cnf(c_92203,plain,
    ( k9_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK415
    | k8_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK414
    | k10_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK416
    | sK412 = o_0_0_xboole_0
    | sK411 = o_0_0_xboole_0
    | sK410 = o_0_0_xboole_0
    | sK409 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_91974,c_2379])).

cnf(c_2201,plain,
    ( ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X1)
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
    | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f7322])).

cnf(c_67704,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X1) != iProver_top
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2201])).

cnf(c_2208,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) ),
    inference(cnf_transformation,[],[f6946])).

cnf(c_67697,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_81978,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_67704,c_67697])).

cnf(c_89115,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) = sK415
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_81978])).

cnf(c_89154,plain,
    ( k9_mcart_1(X0,X1,X2,X3,sK413) = sK415
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_89115,c_2380])).

cnf(c_89265,plain,
    ( k9_mcart_1(sK409,sK410,sK411,sK412,sK413) = sK415
    | sK412 = o_0_0_xboole_0
    | sK411 = o_0_0_xboole_0
    | sK410 = o_0_0_xboole_0
    | sK409 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_67573,c_89154])).

cnf(c_2198,plain,
    ( ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X0)
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
    | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f7320])).

cnf(c_67707,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)),X0) != iProver_top
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2198])).

cnf(c_2207,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) ),
    inference(cnf_transformation,[],[f6945])).

cnf(c_67698,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2207])).

cnf(c_81992,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_67707,c_67698])).

cnf(c_90025,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) = sK414
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_81992])).

cnf(c_90064,plain,
    ( k8_mcart_1(X0,X1,X2,X3,sK413) = sK414
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3
    | m1_subset_1(sK413,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_90025,c_2380])).

cnf(c_90479,plain,
    ( k8_mcart_1(sK409,sK410,sK411,sK412,sK413) = sK414
    | sK412 = o_0_0_xboole_0
    | sK411 = o_0_0_xboole_0
    | sK410 = o_0_0_xboole_0
    | sK409 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_67573,c_90064])).

cnf(c_92229,plain,
    ( k10_mcart_1(sK409,sK410,sK411,sK412,sK413) != sK416
    | sK412 = o_0_0_xboole_0
    | sK411 = o_0_0_xboole_0
    | sK410 = o_0_0_xboole_0
    | sK409 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_92203,c_89265,c_90479])).

cnf(c_2368,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0),X1),X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7335])).

cnf(c_2421,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_2369,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f7029])).

cnf(c_2420,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2369])).

cnf(c_2382,negated_conjecture,
    ( o_0_0_xboole_0 != sK412 ),
    inference(cnf_transformation,[],[f7041])).

cnf(c_2383,negated_conjecture,
    ( o_0_0_xboole_0 != sK411 ),
    inference(cnf_transformation,[],[f7042])).

cnf(c_2384,negated_conjecture,
    ( o_0_0_xboole_0 != sK410 ),
    inference(cnf_transformation,[],[f7043])).

cnf(c_2385,negated_conjecture,
    ( o_0_0_xboole_0 != sK409 ),
    inference(cnf_transformation,[],[f7044])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_92971,c_92704,c_92702,c_92700,c_92698,c_92229,c_2421,c_2420,c_2382,c_2383,c_2384,c_2385])).

%------------------------------------------------------------------------------
