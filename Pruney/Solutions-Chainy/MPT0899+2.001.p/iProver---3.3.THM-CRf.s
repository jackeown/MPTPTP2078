%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:46 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 305 expanded)
%              Number of clauses        :   55 (  89 expanded)
%              Number of leaves         :   18 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  657 (2375 expanded)
%              Number of equality atoms :  542 (2094 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
     => ( ( k11_mcart_1(X0,X1,X2,X3,X4) != sK24
          | k10_mcart_1(X0,X1,X2,X3,X4) != sK23
          | k9_mcart_1(X0,X1,X2,X3,X4) != sK22
          | k8_mcart_1(X0,X1,X2,X3,X4) != sK21 )
        & k4_mcart_1(sK21,sK22,sK23,sK24) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
            ( ( k11_mcart_1(X0,X1,X2,X3,sK20) != X8
              | k10_mcart_1(X0,X1,X2,X3,sK20) != X7
              | k9_mcart_1(X0,X1,X2,X3,sK20) != X6
              | k8_mcart_1(X0,X1,X2,X3,sK20) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = sK20 )
        & m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
              ( ( k11_mcart_1(sK16,sK17,sK18,sK19,X4) != X8
                | k10_mcart_1(sK16,sK17,sK18,sK19,X4) != X7
                | k9_mcart_1(sK16,sK17,sK18,sK19,X4) != X6
                | k8_mcart_1(sK16,sK17,sK18,sK19,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(sK16,sK17,sK18,sK19)) )
      & k1_xboole_0 != sK19
      & k1_xboole_0 != sK18
      & k1_xboole_0 != sK17
      & k1_xboole_0 != sK16 ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
      | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23
      | k9_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK22
      | k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21 )
    & k4_mcart_1(sK21,sK22,sK23,sK24) = sK20
    & m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19))
    & k1_xboole_0 != sK19
    & k1_xboole_0 != sK18
    & k1_xboole_0 != sK17
    & k1_xboole_0 != sK16 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18,sK19,sK20,sK21,sK22,sK23,sK24])],[f19,f38,f37,f36])).

fof(f60,plain,(
    m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19)) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    k4_mcart_1(sK21,sK22,sK23,sK24) = sK20 ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK2(X4,X5) != X5
        & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK2(X4,X5) != X5
                    & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4 ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f22])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f63])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X9
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK7(X4,X5) != X5
        & k4_mcart_1(sK4(X4,X5),sK5(X4,X5),sK6(X4,X5),sK7(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK7(X4,X5) != X5
                    & k4_mcart_1(sK4(X4,X5),sK5(X4,X5),sK6(X4,X5),sK7(X4,X5)) = X4 ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f26])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f66,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f65])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK8(X4,X5) != X5
        & k4_mcart_1(sK8(X4,X5),sK9(X4,X5),sK10(X4,X5),sK11(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK8(X4,X5) != X5
                    & k4_mcart_1(sK8(X4,X5),sK9(X4,X5),sK10(X4,X5),sK11(X4,X5)) = X4 ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f29,f30])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f46])).

fof(f68,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f67])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X7
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK13(X4,X5) != X5
        & k4_mcart_1(sK12(X4,X5),sK13(X4,X5),sK14(X4,X5),sK15(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK13(X4,X5) != X5
                    & k4_mcart_1(sK12(X4,X5),sK13(X4,X5),sK14(X4,X5),sK15(X4,X5)) = X4 ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14,sK15])],[f33,f34])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f49])).

fof(f70,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f69])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    k1_xboole_0 != sK16 ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    k1_xboole_0 != sK17 ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    k1_xboole_0 != sK18 ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    k1_xboole_0 != sK19 ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,
    ( k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
    | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23
    | k9_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK22
    | k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_483,plain,
    ( m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( k4_mcart_1(sK21,sK22,sK23,sK24) = sK20 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2,plain,
    ( ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X2)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_497,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X2) != iProver_top
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_487,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_713,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_497,c_487])).

cnf(c_5439,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK23
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_713])).

cnf(c_5440,plain,
    ( k10_mcart_1(X0,X1,X2,X3,sK20) = sK23
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5439,c_17])).

cnf(c_5449,plain,
    ( k10_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK23
    | sK19 = k1_xboole_0
    | sK18 = k1_xboole_0
    | sK17 = k1_xboole_0
    | sK16 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_483,c_5440])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X3)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_494,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X3) != iProver_top
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_486,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_699,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_494,c_486])).

cnf(c_4730,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK24
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_699])).

cnf(c_4731,plain,
    ( k11_mcart_1(X0,X1,X2,X3,sK20) = sK24
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4730,c_17])).

cnf(c_4812,plain,
    ( k11_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK24
    | sK19 = k1_xboole_0
    | sK18 = k1_xboole_0
    | sK17 = k1_xboole_0
    | sK16 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_483,c_4731])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X0)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_491,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X0) != iProver_top
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_485,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_685,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_491,c_485])).

cnf(c_2380,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK21
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_685])).

cnf(c_2381,plain,
    ( k8_mcart_1(X0,X1,X2,X3,sK20) = sK21
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2380,c_17])).

cnf(c_2390,plain,
    ( k8_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK21
    | sK19 = k1_xboole_0
    | sK18 = k1_xboole_0
    | sK17 = k1_xboole_0
    | sK16 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_483,c_2381])).

cnf(c_11,plain,
    ( ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X1)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_488,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X1) != iProver_top
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_484,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_671,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_488,c_484])).

cnf(c_1579,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK22
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_671])).

cnf(c_1580,plain,
    ( k9_mcart_1(X0,X1,X2,X3,sK20) = sK22
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1579,c_17])).

cnf(c_1749,plain,
    ( k9_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK22
    | sK19 = k1_xboole_0
    | sK18 = k1_xboole_0
    | sK17 = k1_xboole_0
    | sK16 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_483,c_1580])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK16 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK17 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK18 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK19 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_206,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_223,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_207,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_757,plain,
    ( sK19 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK19 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_758,plain,
    ( sK19 != k1_xboole_0
    | k1_xboole_0 = sK19
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_759,plain,
    ( sK18 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK18 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_760,plain,
    ( sK18 != k1_xboole_0
    | k1_xboole_0 = sK18
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_761,plain,
    ( sK17 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK17 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_762,plain,
    ( sK17 != k1_xboole_0
    | k1_xboole_0 = sK17
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_763,plain,
    ( sK16 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK16 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_764,plain,
    ( sK16 != k1_xboole_0
    | k1_xboole_0 = sK16
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1750,plain,
    ( k9_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK22 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1749,c_22,c_21,c_20,c_19,c_223,c_758,c_760,c_762,c_764])).

cnf(c_16,negated_conjecture,
    ( k9_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK22
    | k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21
    | k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
    | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1753,plain,
    ( k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21
    | k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
    | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23
    | sK22 != sK22 ),
    inference(demodulation,[status(thm)],[c_1750,c_16])).

cnf(c_2123,plain,
    ( k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21
    | k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
    | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23 ),
    inference(equality_resolution_simp,[status(thm)],[c_1753])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5449,c_4812,c_2390,c_2123,c_764,c_762,c_760,c_758,c_223,c_19,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:21:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.28/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/0.96  
% 2.28/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.28/0.96  
% 2.28/0.96  ------  iProver source info
% 2.28/0.96  
% 2.28/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.28/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.28/0.96  git: non_committed_changes: false
% 2.28/0.96  git: last_make_outside_of_git: false
% 2.28/0.96  
% 2.28/0.96  ------ 
% 2.28/0.96  
% 2.28/0.96  ------ Input Options
% 2.28/0.96  
% 2.28/0.96  --out_options                           all
% 2.28/0.96  --tptp_safe_out                         true
% 2.28/0.96  --problem_path                          ""
% 2.28/0.96  --include_path                          ""
% 2.28/0.96  --clausifier                            res/vclausify_rel
% 2.28/0.96  --clausifier_options                    --mode clausify
% 2.28/0.96  --stdin                                 false
% 2.28/0.96  --stats_out                             all
% 2.28/0.96  
% 2.28/0.96  ------ General Options
% 2.28/0.96  
% 2.28/0.96  --fof                                   false
% 2.28/0.96  --time_out_real                         305.
% 2.28/0.96  --time_out_virtual                      -1.
% 2.28/0.96  --symbol_type_check                     false
% 2.28/0.96  --clausify_out                          false
% 2.28/0.96  --sig_cnt_out                           false
% 2.28/0.96  --trig_cnt_out                          false
% 2.28/0.96  --trig_cnt_out_tolerance                1.
% 2.28/0.96  --trig_cnt_out_sk_spl                   false
% 2.28/0.96  --abstr_cl_out                          false
% 2.28/0.96  
% 2.28/0.96  ------ Global Options
% 2.28/0.96  
% 2.28/0.96  --schedule                              default
% 2.28/0.96  --add_important_lit                     false
% 2.28/0.96  --prop_solver_per_cl                    1000
% 2.28/0.96  --min_unsat_core                        false
% 2.28/0.96  --soft_assumptions                      false
% 2.28/0.96  --soft_lemma_size                       3
% 2.28/0.96  --prop_impl_unit_size                   0
% 2.28/0.96  --prop_impl_unit                        []
% 2.28/0.96  --share_sel_clauses                     true
% 2.28/0.96  --reset_solvers                         false
% 2.28/0.96  --bc_imp_inh                            [conj_cone]
% 2.28/0.96  --conj_cone_tolerance                   3.
% 2.28/0.96  --extra_neg_conj                        none
% 2.28/0.96  --large_theory_mode                     true
% 2.28/0.96  --prolific_symb_bound                   200
% 2.28/0.96  --lt_threshold                          2000
% 2.28/0.96  --clause_weak_htbl                      true
% 2.28/0.96  --gc_record_bc_elim                     false
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing Options
% 2.28/0.96  
% 2.28/0.96  --preprocessing_flag                    true
% 2.28/0.96  --time_out_prep_mult                    0.1
% 2.28/0.96  --splitting_mode                        input
% 2.28/0.96  --splitting_grd                         true
% 2.28/0.96  --splitting_cvd                         false
% 2.28/0.96  --splitting_cvd_svl                     false
% 2.28/0.96  --splitting_nvd                         32
% 2.28/0.96  --sub_typing                            true
% 2.28/0.96  --prep_gs_sim                           true
% 2.28/0.96  --prep_unflatten                        true
% 2.28/0.96  --prep_res_sim                          true
% 2.28/0.96  --prep_upred                            true
% 2.28/0.96  --prep_sem_filter                       exhaustive
% 2.28/0.96  --prep_sem_filter_out                   false
% 2.28/0.96  --pred_elim                             true
% 2.28/0.96  --res_sim_input                         true
% 2.28/0.96  --eq_ax_congr_red                       true
% 2.28/0.96  --pure_diseq_elim                       true
% 2.28/0.96  --brand_transform                       false
% 2.28/0.96  --non_eq_to_eq                          false
% 2.28/0.96  --prep_def_merge                        true
% 2.28/0.96  --prep_def_merge_prop_impl              false
% 2.28/0.96  --prep_def_merge_mbd                    true
% 2.28/0.96  --prep_def_merge_tr_red                 false
% 2.28/0.96  --prep_def_merge_tr_cl                  false
% 2.28/0.96  --smt_preprocessing                     true
% 2.28/0.96  --smt_ac_axioms                         fast
% 2.28/0.96  --preprocessed_out                      false
% 2.28/0.96  --preprocessed_stats                    false
% 2.28/0.96  
% 2.28/0.96  ------ Abstraction refinement Options
% 2.28/0.96  
% 2.28/0.96  --abstr_ref                             []
% 2.28/0.96  --abstr_ref_prep                        false
% 2.28/0.96  --abstr_ref_until_sat                   false
% 2.28/0.96  --abstr_ref_sig_restrict                funpre
% 2.28/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.96  --abstr_ref_under                       []
% 2.28/0.96  
% 2.28/0.96  ------ SAT Options
% 2.28/0.96  
% 2.28/0.96  --sat_mode                              false
% 2.28/0.96  --sat_fm_restart_options                ""
% 2.28/0.96  --sat_gr_def                            false
% 2.28/0.96  --sat_epr_types                         true
% 2.28/0.96  --sat_non_cyclic_types                  false
% 2.28/0.96  --sat_finite_models                     false
% 2.28/0.96  --sat_fm_lemmas                         false
% 2.28/0.96  --sat_fm_prep                           false
% 2.28/0.96  --sat_fm_uc_incr                        true
% 2.28/0.96  --sat_out_model                         small
% 2.28/0.96  --sat_out_clauses                       false
% 2.28/0.96  
% 2.28/0.96  ------ QBF Options
% 2.28/0.96  
% 2.28/0.96  --qbf_mode                              false
% 2.28/0.96  --qbf_elim_univ                         false
% 2.28/0.96  --qbf_dom_inst                          none
% 2.28/0.96  --qbf_dom_pre_inst                      false
% 2.28/0.96  --qbf_sk_in                             false
% 2.28/0.96  --qbf_pred_elim                         true
% 2.28/0.96  --qbf_split                             512
% 2.28/0.96  
% 2.28/0.96  ------ BMC1 Options
% 2.28/0.96  
% 2.28/0.96  --bmc1_incremental                      false
% 2.28/0.96  --bmc1_axioms                           reachable_all
% 2.28/0.96  --bmc1_min_bound                        0
% 2.28/0.96  --bmc1_max_bound                        -1
% 2.28/0.96  --bmc1_max_bound_default                -1
% 2.28/0.96  --bmc1_symbol_reachability              true
% 2.28/0.96  --bmc1_property_lemmas                  false
% 2.28/0.96  --bmc1_k_induction                      false
% 2.28/0.96  --bmc1_non_equiv_states                 false
% 2.28/0.96  --bmc1_deadlock                         false
% 2.28/0.96  --bmc1_ucm                              false
% 2.28/0.96  --bmc1_add_unsat_core                   none
% 2.28/0.96  --bmc1_unsat_core_children              false
% 2.28/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.96  --bmc1_out_stat                         full
% 2.28/0.96  --bmc1_ground_init                      false
% 2.28/0.96  --bmc1_pre_inst_next_state              false
% 2.28/0.96  --bmc1_pre_inst_state                   false
% 2.28/0.96  --bmc1_pre_inst_reach_state             false
% 2.28/0.96  --bmc1_out_unsat_core                   false
% 2.28/0.96  --bmc1_aig_witness_out                  false
% 2.28/0.96  --bmc1_verbose                          false
% 2.28/0.96  --bmc1_dump_clauses_tptp                false
% 2.28/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.96  --bmc1_dump_file                        -
% 2.28/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.96  --bmc1_ucm_extend_mode                  1
% 2.28/0.96  --bmc1_ucm_init_mode                    2
% 2.28/0.96  --bmc1_ucm_cone_mode                    none
% 2.28/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.96  --bmc1_ucm_relax_model                  4
% 2.28/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.96  --bmc1_ucm_layered_model                none
% 2.28/0.96  --bmc1_ucm_max_lemma_size               10
% 2.28/0.96  
% 2.28/0.96  ------ AIG Options
% 2.28/0.96  
% 2.28/0.96  --aig_mode                              false
% 2.28/0.96  
% 2.28/0.96  ------ Instantiation Options
% 2.28/0.96  
% 2.28/0.96  --instantiation_flag                    true
% 2.28/0.96  --inst_sos_flag                         false
% 2.28/0.96  --inst_sos_phase                        true
% 2.28/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel_side                     num_symb
% 2.28/0.96  --inst_solver_per_active                1400
% 2.28/0.96  --inst_solver_calls_frac                1.
% 2.28/0.96  --inst_passive_queue_type               priority_queues
% 2.28/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.96  --inst_passive_queues_freq              [25;2]
% 2.28/0.96  --inst_dismatching                      true
% 2.28/0.96  --inst_eager_unprocessed_to_passive     true
% 2.28/0.96  --inst_prop_sim_given                   true
% 2.28/0.96  --inst_prop_sim_new                     false
% 2.28/0.96  --inst_subs_new                         false
% 2.28/0.96  --inst_eq_res_simp                      false
% 2.28/0.96  --inst_subs_given                       false
% 2.28/0.96  --inst_orphan_elimination               true
% 2.28/0.96  --inst_learning_loop_flag               true
% 2.28/0.96  --inst_learning_start                   3000
% 2.28/0.96  --inst_learning_factor                  2
% 2.28/0.96  --inst_start_prop_sim_after_learn       3
% 2.28/0.96  --inst_sel_renew                        solver
% 2.28/0.96  --inst_lit_activity_flag                true
% 2.28/0.96  --inst_restr_to_given                   false
% 2.28/0.96  --inst_activity_threshold               500
% 2.28/0.96  --inst_out_proof                        true
% 2.28/0.96  
% 2.28/0.96  ------ Resolution Options
% 2.28/0.96  
% 2.28/0.96  --resolution_flag                       true
% 2.28/0.96  --res_lit_sel                           adaptive
% 2.28/0.96  --res_lit_sel_side                      none
% 2.28/0.96  --res_ordering                          kbo
% 2.28/0.96  --res_to_prop_solver                    active
% 2.28/0.96  --res_prop_simpl_new                    false
% 2.28/0.96  --res_prop_simpl_given                  true
% 2.28/0.96  --res_passive_queue_type                priority_queues
% 2.28/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.96  --res_passive_queues_freq               [15;5]
% 2.28/0.96  --res_forward_subs                      full
% 2.28/0.96  --res_backward_subs                     full
% 2.28/0.96  --res_forward_subs_resolution           true
% 2.28/0.96  --res_backward_subs_resolution          true
% 2.28/0.96  --res_orphan_elimination                true
% 2.28/0.96  --res_time_limit                        2.
% 2.28/0.96  --res_out_proof                         true
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Options
% 2.28/0.96  
% 2.28/0.96  --superposition_flag                    true
% 2.28/0.96  --sup_passive_queue_type                priority_queues
% 2.28/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.96  --demod_completeness_check              fast
% 2.28/0.96  --demod_use_ground                      true
% 2.28/0.96  --sup_to_prop_solver                    passive
% 2.28/0.96  --sup_prop_simpl_new                    true
% 2.28/0.96  --sup_prop_simpl_given                  true
% 2.28/0.96  --sup_fun_splitting                     false
% 2.28/0.96  --sup_smt_interval                      50000
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Simplification Setup
% 2.28/0.96  
% 2.28/0.96  --sup_indices_passive                   []
% 2.28/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_full_bw                           [BwDemod]
% 2.28/0.96  --sup_immed_triv                        [TrivRules]
% 2.28/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_immed_bw_main                     []
% 2.28/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  
% 2.28/0.96  ------ Combination Options
% 2.28/0.96  
% 2.28/0.96  --comb_res_mult                         3
% 2.28/0.96  --comb_sup_mult                         2
% 2.28/0.96  --comb_inst_mult                        10
% 2.28/0.96  
% 2.28/0.96  ------ Debug Options
% 2.28/0.96  
% 2.28/0.96  --dbg_backtrace                         false
% 2.28/0.96  --dbg_dump_prop_clauses                 false
% 2.28/0.96  --dbg_dump_prop_clauses_file            -
% 2.28/0.96  --dbg_out_stat                          false
% 2.28/0.96  ------ Parsing...
% 2.28/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.28/0.96  ------ Proving...
% 2.28/0.96  ------ Problem Properties 
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  clauses                                 23
% 2.28/0.96  conjectures                             7
% 2.28/0.96  EPR                                     4
% 2.28/0.96  Horn                                    11
% 2.28/0.96  unary                                   6
% 2.28/0.96  binary                                  4
% 2.28/0.96  lits                                    110
% 2.28/0.96  lits eq                                 77
% 2.28/0.96  fd_pure                                 0
% 2.28/0.96  fd_pseudo                               0
% 2.28/0.96  fd_cond                                 0
% 2.28/0.96  fd_pseudo_cond                          4
% 2.28/0.96  AC symbols                              0
% 2.28/0.96  
% 2.28/0.96  ------ Schedule dynamic 5 is on 
% 2.28/0.96  
% 2.28/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  ------ 
% 2.28/0.96  Current options:
% 2.28/0.96  ------ 
% 2.28/0.96  
% 2.28/0.96  ------ Input Options
% 2.28/0.96  
% 2.28/0.96  --out_options                           all
% 2.28/0.96  --tptp_safe_out                         true
% 2.28/0.96  --problem_path                          ""
% 2.28/0.96  --include_path                          ""
% 2.28/0.96  --clausifier                            res/vclausify_rel
% 2.28/0.96  --clausifier_options                    --mode clausify
% 2.28/0.96  --stdin                                 false
% 2.28/0.96  --stats_out                             all
% 2.28/0.96  
% 2.28/0.96  ------ General Options
% 2.28/0.96  
% 2.28/0.96  --fof                                   false
% 2.28/0.96  --time_out_real                         305.
% 2.28/0.96  --time_out_virtual                      -1.
% 2.28/0.96  --symbol_type_check                     false
% 2.28/0.96  --clausify_out                          false
% 2.28/0.96  --sig_cnt_out                           false
% 2.28/0.96  --trig_cnt_out                          false
% 2.28/0.96  --trig_cnt_out_tolerance                1.
% 2.28/0.96  --trig_cnt_out_sk_spl                   false
% 2.28/0.96  --abstr_cl_out                          false
% 2.28/0.96  
% 2.28/0.96  ------ Global Options
% 2.28/0.96  
% 2.28/0.96  --schedule                              default
% 2.28/0.96  --add_important_lit                     false
% 2.28/0.96  --prop_solver_per_cl                    1000
% 2.28/0.96  --min_unsat_core                        false
% 2.28/0.96  --soft_assumptions                      false
% 2.28/0.96  --soft_lemma_size                       3
% 2.28/0.96  --prop_impl_unit_size                   0
% 2.28/0.96  --prop_impl_unit                        []
% 2.28/0.96  --share_sel_clauses                     true
% 2.28/0.96  --reset_solvers                         false
% 2.28/0.96  --bc_imp_inh                            [conj_cone]
% 2.28/0.96  --conj_cone_tolerance                   3.
% 2.28/0.96  --extra_neg_conj                        none
% 2.28/0.96  --large_theory_mode                     true
% 2.28/0.96  --prolific_symb_bound                   200
% 2.28/0.96  --lt_threshold                          2000
% 2.28/0.96  --clause_weak_htbl                      true
% 2.28/0.96  --gc_record_bc_elim                     false
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing Options
% 2.28/0.96  
% 2.28/0.96  --preprocessing_flag                    true
% 2.28/0.96  --time_out_prep_mult                    0.1
% 2.28/0.96  --splitting_mode                        input
% 2.28/0.96  --splitting_grd                         true
% 2.28/0.96  --splitting_cvd                         false
% 2.28/0.96  --splitting_cvd_svl                     false
% 2.28/0.96  --splitting_nvd                         32
% 2.28/0.96  --sub_typing                            true
% 2.28/0.96  --prep_gs_sim                           true
% 2.28/0.96  --prep_unflatten                        true
% 2.28/0.96  --prep_res_sim                          true
% 2.28/0.96  --prep_upred                            true
% 2.28/0.96  --prep_sem_filter                       exhaustive
% 2.28/0.96  --prep_sem_filter_out                   false
% 2.28/0.96  --pred_elim                             true
% 2.28/0.96  --res_sim_input                         true
% 2.28/0.96  --eq_ax_congr_red                       true
% 2.28/0.96  --pure_diseq_elim                       true
% 2.28/0.96  --brand_transform                       false
% 2.28/0.96  --non_eq_to_eq                          false
% 2.28/0.96  --prep_def_merge                        true
% 2.28/0.96  --prep_def_merge_prop_impl              false
% 2.28/0.96  --prep_def_merge_mbd                    true
% 2.28/0.96  --prep_def_merge_tr_red                 false
% 2.28/0.96  --prep_def_merge_tr_cl                  false
% 2.28/0.96  --smt_preprocessing                     true
% 2.28/0.96  --smt_ac_axioms                         fast
% 2.28/0.96  --preprocessed_out                      false
% 2.28/0.96  --preprocessed_stats                    false
% 2.28/0.96  
% 2.28/0.96  ------ Abstraction refinement Options
% 2.28/0.96  
% 2.28/0.96  --abstr_ref                             []
% 2.28/0.96  --abstr_ref_prep                        false
% 2.28/0.96  --abstr_ref_until_sat                   false
% 2.28/0.96  --abstr_ref_sig_restrict                funpre
% 2.28/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.96  --abstr_ref_under                       []
% 2.28/0.96  
% 2.28/0.96  ------ SAT Options
% 2.28/0.96  
% 2.28/0.96  --sat_mode                              false
% 2.28/0.96  --sat_fm_restart_options                ""
% 2.28/0.96  --sat_gr_def                            false
% 2.28/0.96  --sat_epr_types                         true
% 2.28/0.96  --sat_non_cyclic_types                  false
% 2.28/0.96  --sat_finite_models                     false
% 2.28/0.96  --sat_fm_lemmas                         false
% 2.28/0.96  --sat_fm_prep                           false
% 2.28/0.96  --sat_fm_uc_incr                        true
% 2.28/0.96  --sat_out_model                         small
% 2.28/0.96  --sat_out_clauses                       false
% 2.28/0.96  
% 2.28/0.96  ------ QBF Options
% 2.28/0.96  
% 2.28/0.96  --qbf_mode                              false
% 2.28/0.96  --qbf_elim_univ                         false
% 2.28/0.96  --qbf_dom_inst                          none
% 2.28/0.96  --qbf_dom_pre_inst                      false
% 2.28/0.96  --qbf_sk_in                             false
% 2.28/0.96  --qbf_pred_elim                         true
% 2.28/0.96  --qbf_split                             512
% 2.28/0.96  
% 2.28/0.96  ------ BMC1 Options
% 2.28/0.96  
% 2.28/0.96  --bmc1_incremental                      false
% 2.28/0.96  --bmc1_axioms                           reachable_all
% 2.28/0.96  --bmc1_min_bound                        0
% 2.28/0.96  --bmc1_max_bound                        -1
% 2.28/0.96  --bmc1_max_bound_default                -1
% 2.28/0.96  --bmc1_symbol_reachability              true
% 2.28/0.96  --bmc1_property_lemmas                  false
% 2.28/0.96  --bmc1_k_induction                      false
% 2.28/0.96  --bmc1_non_equiv_states                 false
% 2.28/0.96  --bmc1_deadlock                         false
% 2.28/0.96  --bmc1_ucm                              false
% 2.28/0.96  --bmc1_add_unsat_core                   none
% 2.28/0.96  --bmc1_unsat_core_children              false
% 2.28/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.96  --bmc1_out_stat                         full
% 2.28/0.96  --bmc1_ground_init                      false
% 2.28/0.96  --bmc1_pre_inst_next_state              false
% 2.28/0.96  --bmc1_pre_inst_state                   false
% 2.28/0.96  --bmc1_pre_inst_reach_state             false
% 2.28/0.96  --bmc1_out_unsat_core                   false
% 2.28/0.96  --bmc1_aig_witness_out                  false
% 2.28/0.96  --bmc1_verbose                          false
% 2.28/0.96  --bmc1_dump_clauses_tptp                false
% 2.28/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.96  --bmc1_dump_file                        -
% 2.28/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.96  --bmc1_ucm_extend_mode                  1
% 2.28/0.96  --bmc1_ucm_init_mode                    2
% 2.28/0.96  --bmc1_ucm_cone_mode                    none
% 2.28/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.96  --bmc1_ucm_relax_model                  4
% 2.28/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.96  --bmc1_ucm_layered_model                none
% 2.28/0.96  --bmc1_ucm_max_lemma_size               10
% 2.28/0.96  
% 2.28/0.96  ------ AIG Options
% 2.28/0.96  
% 2.28/0.96  --aig_mode                              false
% 2.28/0.96  
% 2.28/0.96  ------ Instantiation Options
% 2.28/0.96  
% 2.28/0.96  --instantiation_flag                    true
% 2.28/0.96  --inst_sos_flag                         false
% 2.28/0.96  --inst_sos_phase                        true
% 2.28/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel_side                     none
% 2.28/0.96  --inst_solver_per_active                1400
% 2.28/0.96  --inst_solver_calls_frac                1.
% 2.28/0.96  --inst_passive_queue_type               priority_queues
% 2.28/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.96  --inst_passive_queues_freq              [25;2]
% 2.28/0.96  --inst_dismatching                      true
% 2.28/0.96  --inst_eager_unprocessed_to_passive     true
% 2.28/0.96  --inst_prop_sim_given                   true
% 2.28/0.96  --inst_prop_sim_new                     false
% 2.28/0.96  --inst_subs_new                         false
% 2.28/0.96  --inst_eq_res_simp                      false
% 2.28/0.96  --inst_subs_given                       false
% 2.28/0.96  --inst_orphan_elimination               true
% 2.28/0.96  --inst_learning_loop_flag               true
% 2.28/0.96  --inst_learning_start                   3000
% 2.28/0.96  --inst_learning_factor                  2
% 2.28/0.96  --inst_start_prop_sim_after_learn       3
% 2.28/0.96  --inst_sel_renew                        solver
% 2.28/0.96  --inst_lit_activity_flag                true
% 2.28/0.96  --inst_restr_to_given                   false
% 2.28/0.96  --inst_activity_threshold               500
% 2.28/0.96  --inst_out_proof                        true
% 2.28/0.96  
% 2.28/0.96  ------ Resolution Options
% 2.28/0.96  
% 2.28/0.96  --resolution_flag                       false
% 2.28/0.96  --res_lit_sel                           adaptive
% 2.28/0.96  --res_lit_sel_side                      none
% 2.28/0.96  --res_ordering                          kbo
% 2.28/0.96  --res_to_prop_solver                    active
% 2.28/0.96  --res_prop_simpl_new                    false
% 2.28/0.96  --res_prop_simpl_given                  true
% 2.28/0.96  --res_passive_queue_type                priority_queues
% 2.28/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.96  --res_passive_queues_freq               [15;5]
% 2.28/0.96  --res_forward_subs                      full
% 2.28/0.96  --res_backward_subs                     full
% 2.28/0.96  --res_forward_subs_resolution           true
% 2.28/0.96  --res_backward_subs_resolution          true
% 2.28/0.96  --res_orphan_elimination                true
% 2.28/0.96  --res_time_limit                        2.
% 2.28/0.96  --res_out_proof                         true
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Options
% 2.28/0.96  
% 2.28/0.96  --superposition_flag                    true
% 2.28/0.96  --sup_passive_queue_type                priority_queues
% 2.28/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.96  --demod_completeness_check              fast
% 2.28/0.96  --demod_use_ground                      true
% 2.28/0.96  --sup_to_prop_solver                    passive
% 2.28/0.96  --sup_prop_simpl_new                    true
% 2.28/0.96  --sup_prop_simpl_given                  true
% 2.28/0.96  --sup_fun_splitting                     false
% 2.28/0.96  --sup_smt_interval                      50000
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Simplification Setup
% 2.28/0.96  
% 2.28/0.96  --sup_indices_passive                   []
% 2.28/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_full_bw                           [BwDemod]
% 2.28/0.96  --sup_immed_triv                        [TrivRules]
% 2.28/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_immed_bw_main                     []
% 2.28/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  
% 2.28/0.96  ------ Combination Options
% 2.28/0.96  
% 2.28/0.96  --comb_res_mult                         3
% 2.28/0.96  --comb_sup_mult                         2
% 2.28/0.96  --comb_inst_mult                        10
% 2.28/0.96  
% 2.28/0.96  ------ Debug Options
% 2.28/0.96  
% 2.28/0.96  --dbg_backtrace                         false
% 2.28/0.96  --dbg_dump_prop_clauses                 false
% 2.28/0.96  --dbg_dump_prop_clauses_file            -
% 2.28/0.96  --dbg_out_stat                          false
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  ------ Proving...
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  % SZS status Theorem for theBenchmark.p
% 2.28/0.96  
% 2.28/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.28/0.96  
% 2.28/0.96  fof(f9,conjecture,(
% 2.28/0.96    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f10,negated_conjecture,(
% 2.28/0.96    ~! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.28/0.96    inference(negated_conjecture,[],[f9])).
% 2.28/0.96  
% 2.28/0.96  fof(f19,plain,(
% 2.28/0.96    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.28/0.96    inference(ennf_transformation,[],[f10])).
% 2.28/0.96  
% 2.28/0.96  fof(f38,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) => ((k11_mcart_1(X0,X1,X2,X3,X4) != sK24 | k10_mcart_1(X0,X1,X2,X3,X4) != sK23 | k9_mcart_1(X0,X1,X2,X3,X4) != sK22 | k8_mcart_1(X0,X1,X2,X3,X4) != sK21) & k4_mcart_1(sK21,sK22,sK23,sK24) = X4)) )),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f37,plain,(
% 2.28/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) => (? [X8,X7,X6,X5] : ((k11_mcart_1(X0,X1,X2,X3,sK20) != X8 | k10_mcart_1(X0,X1,X2,X3,sK20) != X7 | k9_mcart_1(X0,X1,X2,X3,sK20) != X6 | k8_mcart_1(X0,X1,X2,X3,sK20) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK20) & m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f36,plain,(
% 2.28/0.96    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X4] : (? [X8,X7,X6,X5] : ((k11_mcart_1(sK16,sK17,sK18,sK19,X4) != X8 | k10_mcart_1(sK16,sK17,sK18,sK19,X4) != X7 | k9_mcart_1(sK16,sK17,sK18,sK19,X4) != X6 | k8_mcart_1(sK16,sK17,sK18,sK19,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(sK16,sK17,sK18,sK19))) & k1_xboole_0 != sK19 & k1_xboole_0 != sK18 & k1_xboole_0 != sK17 & k1_xboole_0 != sK16)),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f39,plain,(
% 2.28/0.96    (((k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24 | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23 | k9_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK22 | k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21) & k4_mcart_1(sK21,sK22,sK23,sK24) = sK20) & m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19))) & k1_xboole_0 != sK19 & k1_xboole_0 != sK18 & k1_xboole_0 != sK17 & k1_xboole_0 != sK16),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18,sK19,sK20,sK21,sK22,sK23,sK24])],[f19,f38,f37,f36])).
% 2.28/0.96  
% 2.28/0.96  fof(f60,plain,(
% 2.28/0.96    m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19))),
% 2.28/0.96    inference(cnf_transformation,[],[f39])).
% 2.28/0.96  
% 2.28/0.96  fof(f61,plain,(
% 2.28/0.96    k4_mcart_1(sK21,sK22,sK23,sK24) = sK20),
% 2.28/0.96    inference(cnf_transformation,[],[f39])).
% 2.28/0.96  
% 2.28/0.96  fof(f1,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X2) => (k10_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X8)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f11,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k10_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X8 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(ennf_transformation,[],[f1])).
% 2.28/0.96  
% 2.28/0.96  fof(f20,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X8 | k4_mcart_1(X6,X7,X8,X9) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(nnf_transformation,[],[f11])).
% 2.28/0.96  
% 2.28/0.96  fof(f21,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(rectify,[],[f20])).
% 2.28/0.96  
% 2.28/0.96  fof(f22,plain,(
% 2.28/0.96    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK2(X4,X5) != X5 & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4))),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f23,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK2(X4,X5) != X5 & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f22])).
% 2.28/0.96  
% 2.28/0.96  fof(f40,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(cnf_transformation,[],[f23])).
% 2.28/0.96  
% 2.28/0.96  fof(f63,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X12 | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X2) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f40])).
% 2.28/0.96  
% 2.28/0.96  fof(f64,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12 | ~m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X2) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f63])).
% 2.28/0.96  
% 2.28/0.96  fof(f5,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f15,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.28/0.96    inference(ennf_transformation,[],[f5])).
% 2.28/0.96  
% 2.28/0.96  fof(f52,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.28/0.96    inference(cnf_transformation,[],[f15])).
% 2.28/0.96  
% 2.28/0.96  fof(f2,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X3) => (k11_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X9)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f12,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X9 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(ennf_transformation,[],[f2])).
% 2.28/0.96  
% 2.28/0.96  fof(f24,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k11_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X9 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X9 | k4_mcart_1(X6,X7,X8,X9) != X4) | k11_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(nnf_transformation,[],[f12])).
% 2.28/0.96  
% 2.28/0.96  fof(f25,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k11_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X9 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X13 | k4_mcart_1(X10,X11,X12,X13) != X4) | k11_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(rectify,[],[f24])).
% 2.28/0.96  
% 2.28/0.96  fof(f26,plain,(
% 2.28/0.96    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X9 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK7(X4,X5) != X5 & k4_mcart_1(sK4(X4,X5),sK5(X4,X5),sK6(X4,X5),sK7(X4,X5)) = X4))),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f27,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k11_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK7(X4,X5) != X5 & k4_mcart_1(sK4(X4,X5),sK5(X4,X5),sK6(X4,X5),sK7(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X13 | k4_mcart_1(X10,X11,X12,X13) != X4) | k11_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f26])).
% 2.28/0.96  
% 2.28/0.96  fof(f43,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X13 | k4_mcart_1(X10,X11,X12,X13) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(cnf_transformation,[],[f27])).
% 2.28/0.96  
% 2.28/0.96  fof(f65,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X13 | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X3) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f43])).
% 2.28/0.96  
% 2.28/0.96  fof(f66,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13 | ~m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X3) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f65])).
% 2.28/0.96  
% 2.28/0.96  fof(f6,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f16,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.28/0.96    inference(ennf_transformation,[],[f6])).
% 2.28/0.96  
% 2.28/0.96  fof(f53,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.28/0.96    inference(cnf_transformation,[],[f16])).
% 2.28/0.96  
% 2.28/0.96  fof(f3,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X0) => (k8_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X6)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f13,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k8_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X6 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(ennf_transformation,[],[f3])).
% 2.28/0.96  
% 2.28/0.96  fof(f28,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X6 | k4_mcart_1(X6,X7,X8,X9) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(nnf_transformation,[],[f13])).
% 2.28/0.96  
% 2.28/0.96  fof(f29,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(rectify,[],[f28])).
% 2.28/0.96  
% 2.28/0.96  fof(f30,plain,(
% 2.28/0.96    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK8(X4,X5) != X5 & k4_mcart_1(sK8(X4,X5),sK9(X4,X5),sK10(X4,X5),sK11(X4,X5)) = X4))),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f31,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK8(X4,X5) != X5 & k4_mcart_1(sK8(X4,X5),sK9(X4,X5),sK10(X4,X5),sK11(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f29,f30])).
% 2.28/0.96  
% 2.28/0.96  fof(f46,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(cnf_transformation,[],[f31])).
% 2.28/0.96  
% 2.28/0.96  fof(f67,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X10 | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X0) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f46])).
% 2.28/0.96  
% 2.28/0.96  fof(f68,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10 | ~m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X0) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f67])).
% 2.28/0.96  
% 2.28/0.96  fof(f7,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f17,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.28/0.96    inference(ennf_transformation,[],[f7])).
% 2.28/0.96  
% 2.28/0.96  fof(f54,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.28/0.96    inference(cnf_transformation,[],[f17])).
% 2.28/0.96  
% 2.28/0.96  fof(f4,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X1) => (k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X7)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f14,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X7 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(ennf_transformation,[],[f4])).
% 2.28/0.96  
% 2.28/0.96  fof(f32,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X7 | k4_mcart_1(X6,X7,X8,X9) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(nnf_transformation,[],[f14])).
% 2.28/0.96  
% 2.28/0.96  fof(f33,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(rectify,[],[f32])).
% 2.28/0.96  
% 2.28/0.96  fof(f34,plain,(
% 2.28/0.96    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK13(X4,X5) != X5 & k4_mcart_1(sK12(X4,X5),sK13(X4,X5),sK14(X4,X5),sK15(X4,X5)) = X4))),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f35,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK13(X4,X5) != X5 & k4_mcart_1(sK12(X4,X5),sK13(X4,X5),sK14(X4,X5),sK15(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14,sK15])],[f33,f34])).
% 2.28/0.96  
% 2.28/0.96  fof(f49,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(cnf_transformation,[],[f35])).
% 2.28/0.96  
% 2.28/0.96  fof(f69,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X11 | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X1) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f49])).
% 2.28/0.96  
% 2.28/0.96  fof(f70,plain,(
% 2.28/0.96    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11 | ~m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.28/0.96    inference(equality_resolution,[],[f69])).
% 2.28/0.96  
% 2.28/0.96  fof(f8,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 2.28/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f18,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 2.28/0.96    inference(ennf_transformation,[],[f8])).
% 2.28/0.96  
% 2.28/0.96  fof(f55,plain,(
% 2.28/0.96    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 2.28/0.96    inference(cnf_transformation,[],[f18])).
% 2.28/0.96  
% 2.28/0.96  fof(f56,plain,(
% 2.28/0.96    k1_xboole_0 != sK16),
% 2.28/0.96    inference(cnf_transformation,[],[f39])).
% 2.28/0.96  
% 2.28/0.96  fof(f57,plain,(
% 2.28/0.96    k1_xboole_0 != sK17),
% 2.28/0.96    inference(cnf_transformation,[],[f39])).
% 2.28/0.96  
% 2.28/0.96  fof(f58,plain,(
% 2.28/0.96    k1_xboole_0 != sK18),
% 2.28/0.96    inference(cnf_transformation,[],[f39])).
% 2.28/0.96  
% 2.28/0.96  fof(f59,plain,(
% 2.28/0.96    k1_xboole_0 != sK19),
% 2.28/0.96    inference(cnf_transformation,[],[f39])).
% 2.28/0.96  
% 2.28/0.96  fof(f62,plain,(
% 2.28/0.96    k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24 | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23 | k9_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK22 | k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21),
% 2.28/0.96    inference(cnf_transformation,[],[f39])).
% 2.28/0.96  
% 2.28/0.96  cnf(c_18,negated_conjecture,
% 2.28/0.96      ( m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19)) ),
% 2.28/0.96      inference(cnf_transformation,[],[f60]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_483,plain,
% 2.28/0.96      ( m1_subset_1(sK20,k4_zfmisc_1(sK16,sK17,sK18,sK19)) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_17,negated_conjecture,
% 2.28/0.96      ( k4_mcart_1(sK21,sK22,sK23,sK24) = sK20 ),
% 2.28/0.96      inference(cnf_transformation,[],[f61]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_2,plain,
% 2.28/0.96      ( ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X2)
% 2.28/0.96      | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
% 2.28/0.96      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0 ),
% 2.28/0.96      inference(cnf_transformation,[],[f64]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_497,plain,
% 2.28/0.96      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X2) != iProver_top
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_12,plain,
% 2.28/0.96      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.28/0.96      | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) ),
% 2.28/0.96      inference(cnf_transformation,[],[f52]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_487,plain,
% 2.28/0.96      ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
% 2.28/0.96      | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_713,plain,
% 2.28/0.96      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(forward_subsumption_resolution,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_497,c_487]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_5439,plain,
% 2.28/0.96      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK23
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_17,c_713]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_5440,plain,
% 2.28/0.96      ( k10_mcart_1(X0,X1,X2,X3,sK20) = sK23
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(light_normalisation,[status(thm)],[c_5439,c_17]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_5449,plain,
% 2.28/0.96      ( k10_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK23
% 2.28/0.96      | sK19 = k1_xboole_0
% 2.28/0.96      | sK18 = k1_xboole_0
% 2.28/0.96      | sK17 = k1_xboole_0
% 2.28/0.96      | sK16 = k1_xboole_0 ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_483,c_5440]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_5,plain,
% 2.28/0.96      ( ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X3)
% 2.28/0.96      | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
% 2.28/0.96      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0 ),
% 2.28/0.96      inference(cnf_transformation,[],[f66]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_494,plain,
% 2.28/0.96      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X3) != iProver_top
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_13,plain,
% 2.28/0.96      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.28/0.96      | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) ),
% 2.28/0.96      inference(cnf_transformation,[],[f53]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_486,plain,
% 2.28/0.96      ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
% 2.28/0.96      | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_699,plain,
% 2.28/0.96      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(forward_subsumption_resolution,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_494,c_486]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_4730,plain,
% 2.28/0.96      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK24
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_17,c_699]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_4731,plain,
% 2.28/0.96      ( k11_mcart_1(X0,X1,X2,X3,sK20) = sK24
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(light_normalisation,[status(thm)],[c_4730,c_17]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_4812,plain,
% 2.28/0.96      ( k11_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK24
% 2.28/0.96      | sK19 = k1_xboole_0
% 2.28/0.96      | sK18 = k1_xboole_0
% 2.28/0.96      | sK17 = k1_xboole_0
% 2.28/0.96      | sK16 = k1_xboole_0 ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_483,c_4731]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_8,plain,
% 2.28/0.96      ( ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X0)
% 2.28/0.96      | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
% 2.28/0.96      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0 ),
% 2.28/0.96      inference(cnf_transformation,[],[f68]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_491,plain,
% 2.28/0.96      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X0) != iProver_top
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_14,plain,
% 2.28/0.96      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.28/0.96      | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) ),
% 2.28/0.96      inference(cnf_transformation,[],[f54]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_485,plain,
% 2.28/0.96      ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
% 2.28/0.96      | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_685,plain,
% 2.28/0.96      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(forward_subsumption_resolution,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_491,c_485]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_2380,plain,
% 2.28/0.96      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK21
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_17,c_685]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_2381,plain,
% 2.28/0.96      ( k8_mcart_1(X0,X1,X2,X3,sK20) = sK21
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(light_normalisation,[status(thm)],[c_2380,c_17]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_2390,plain,
% 2.28/0.96      ( k8_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK21
% 2.28/0.96      | sK19 = k1_xboole_0
% 2.28/0.96      | sK18 = k1_xboole_0
% 2.28/0.96      | sK17 = k1_xboole_0
% 2.28/0.96      | sK16 = k1_xboole_0 ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_483,c_2381]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_11,plain,
% 2.28/0.96      ( ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X1)
% 2.28/0.96      | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
% 2.28/0.96      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0 ),
% 2.28/0.96      inference(cnf_transformation,[],[f70]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_488,plain,
% 2.28/0.96      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X1) != iProver_top
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_15,plain,
% 2.28/0.96      ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
% 2.28/0.96      | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) ),
% 2.28/0.96      inference(cnf_transformation,[],[f55]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_484,plain,
% 2.28/0.96      ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
% 2.28/0.96      | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_671,plain,
% 2.28/0.96      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(forward_subsumption_resolution,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_488,c_484]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1579,plain,
% 2.28/0.96      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK21,sK22,sK23,sK24)) = sK22
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_17,c_671]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1580,plain,
% 2.28/0.96      ( k9_mcart_1(X0,X1,X2,X3,sK20) = sK22
% 2.28/0.96      | k1_xboole_0 = X3
% 2.28/0.96      | k1_xboole_0 = X2
% 2.28/0.96      | k1_xboole_0 = X1
% 2.28/0.96      | k1_xboole_0 = X0
% 2.28/0.96      | m1_subset_1(sK20,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
% 2.28/0.96      inference(light_normalisation,[status(thm)],[c_1579,c_17]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1749,plain,
% 2.28/0.96      ( k9_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK22
% 2.28/0.96      | sK19 = k1_xboole_0
% 2.28/0.96      | sK18 = k1_xboole_0
% 2.28/0.96      | sK17 = k1_xboole_0
% 2.28/0.96      | sK16 = k1_xboole_0 ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_483,c_1580]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_22,negated_conjecture,
% 2.28/0.96      ( k1_xboole_0 != sK16 ),
% 2.28/0.96      inference(cnf_transformation,[],[f56]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_21,negated_conjecture,
% 2.28/0.96      ( k1_xboole_0 != sK17 ),
% 2.28/0.96      inference(cnf_transformation,[],[f57]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_20,negated_conjecture,
% 2.28/0.96      ( k1_xboole_0 != sK18 ),
% 2.28/0.96      inference(cnf_transformation,[],[f58]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_19,negated_conjecture,
% 2.28/0.96      ( k1_xboole_0 != sK19 ),
% 2.28/0.96      inference(cnf_transformation,[],[f59]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_206,plain,( X0 = X0 ),theory(equality) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_223,plain,
% 2.28/0.96      ( k1_xboole_0 = k1_xboole_0 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_206]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_207,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_757,plain,
% 2.28/0.96      ( sK19 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK19 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_207]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_758,plain,
% 2.28/0.96      ( sK19 != k1_xboole_0
% 2.28/0.96      | k1_xboole_0 = sK19
% 2.28/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_757]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_759,plain,
% 2.28/0.96      ( sK18 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK18 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_207]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_760,plain,
% 2.28/0.96      ( sK18 != k1_xboole_0
% 2.28/0.96      | k1_xboole_0 = sK18
% 2.28/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_759]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_761,plain,
% 2.28/0.96      ( sK17 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK17 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_207]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_762,plain,
% 2.28/0.96      ( sK17 != k1_xboole_0
% 2.28/0.96      | k1_xboole_0 = sK17
% 2.28/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_761]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_763,plain,
% 2.28/0.96      ( sK16 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK16 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_207]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_764,plain,
% 2.28/0.96      ( sK16 != k1_xboole_0
% 2.28/0.96      | k1_xboole_0 = sK16
% 2.28/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_763]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1750,plain,
% 2.28/0.96      ( k9_mcart_1(sK16,sK17,sK18,sK19,sK20) = sK22 ),
% 2.28/0.96      inference(global_propositional_subsumption,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_1749,c_22,c_21,c_20,c_19,c_223,c_758,c_760,c_762,
% 2.28/0.96                 c_764]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_16,negated_conjecture,
% 2.28/0.96      ( k9_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK22
% 2.28/0.96      | k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21
% 2.28/0.96      | k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
% 2.28/0.96      | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23 ),
% 2.28/0.96      inference(cnf_transformation,[],[f62]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1753,plain,
% 2.28/0.96      ( k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21
% 2.28/0.96      | k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
% 2.28/0.96      | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23
% 2.28/0.96      | sK22 != sK22 ),
% 2.28/0.96      inference(demodulation,[status(thm)],[c_1750,c_16]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_2123,plain,
% 2.28/0.96      ( k8_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK21
% 2.28/0.96      | k11_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK24
% 2.28/0.96      | k10_mcart_1(sK16,sK17,sK18,sK19,sK20) != sK23 ),
% 2.28/0.96      inference(equality_resolution_simp,[status(thm)],[c_1753]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(contradiction,plain,
% 2.28/0.96      ( $false ),
% 2.28/0.96      inference(minisat,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_5449,c_4812,c_2390,c_2123,c_764,c_762,c_760,c_758,
% 2.28/0.96                 c_223,c_19,c_20,c_21,c_22]) ).
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.28/0.96  
% 2.28/0.96  ------                               Statistics
% 2.28/0.96  
% 2.28/0.96  ------ General
% 2.28/0.96  
% 2.28/0.96  abstr_ref_over_cycles:                  0
% 2.28/0.96  abstr_ref_under_cycles:                 0
% 2.28/0.96  gc_basic_clause_elim:                   0
% 2.28/0.96  forced_gc_time:                         0
% 2.28/0.96  parsing_time:                           0.01
% 2.28/0.96  unif_index_cands_time:                  0.
% 2.28/0.96  unif_index_add_time:                    0.
% 2.28/0.96  orderings_time:                         0.
% 2.28/0.96  out_proof_time:                         0.009
% 2.28/0.96  total_time:                             0.235
% 2.28/0.96  num_of_symbols:                         64
% 2.28/0.96  num_of_terms:                           13451
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing
% 2.28/0.96  
% 2.28/0.96  num_of_splits:                          0
% 2.28/0.96  num_of_split_atoms:                     0
% 2.28/0.96  num_of_reused_defs:                     0
% 2.28/0.96  num_eq_ax_congr_red:                    64
% 2.28/0.96  num_of_sem_filtered_clauses:            1
% 2.28/0.96  num_of_subtypes:                        0
% 2.28/0.96  monotx_restored_types:                  0
% 2.28/0.96  sat_num_of_epr_types:                   0
% 2.28/0.96  sat_num_of_non_cyclic_types:            0
% 2.28/0.96  sat_guarded_non_collapsed_types:        0
% 2.28/0.96  num_pure_diseq_elim:                    0
% 2.28/0.96  simp_replaced_by:                       0
% 2.28/0.96  res_preprocessed:                       88
% 2.28/0.96  prep_upred:                             0
% 2.28/0.96  prep_unflattend:                        0
% 2.28/0.96  smt_new_axioms:                         0
% 2.28/0.96  pred_elim_cands:                        1
% 2.28/0.96  pred_elim:                              0
% 2.28/0.96  pred_elim_cl:                           0
% 2.28/0.96  pred_elim_cycles:                       1
% 2.28/0.96  merged_defs:                            0
% 2.28/0.96  merged_defs_ncl:                        0
% 2.28/0.96  bin_hyper_res:                          0
% 2.28/0.96  prep_cycles:                            3
% 2.28/0.96  pred_elim_time:                         0.
% 2.28/0.96  splitting_time:                         0.
% 2.28/0.96  sem_filter_time:                        0.
% 2.28/0.96  monotx_time:                            0.001
% 2.28/0.96  subtype_inf_time:                       0.
% 2.28/0.96  
% 2.28/0.96  ------ Problem properties
% 2.28/0.96  
% 2.28/0.96  clauses:                                23
% 2.28/0.96  conjectures:                            7
% 2.28/0.96  epr:                                    4
% 2.28/0.96  horn:                                   11
% 2.28/0.96  ground:                                 7
% 2.28/0.96  unary:                                  6
% 2.28/0.96  binary:                                 4
% 2.28/0.96  lits:                                   110
% 2.28/0.96  lits_eq:                                77
% 2.28/0.96  fd_pure:                                0
% 2.28/0.96  fd_pseudo:                              0
% 2.28/0.96  fd_cond:                                0
% 2.28/0.96  fd_pseudo_cond:                         4
% 2.28/0.96  ac_symbols:                             0
% 2.28/0.96  
% 2.28/0.96  ------ Propositional Solver
% 2.28/0.96  
% 2.28/0.96  prop_solver_calls:                      22
% 2.28/0.96  prop_fast_solver_calls:                 1062
% 2.28/0.96  smt_solver_calls:                       0
% 2.28/0.96  smt_fast_solver_calls:                  0
% 2.28/0.96  prop_num_of_clauses:                    2340
% 2.28/0.96  prop_preprocess_simplified:             7197
% 2.28/0.96  prop_fo_subsumed:                       31
% 2.28/0.96  prop_solver_time:                       0.
% 2.28/0.96  smt_solver_time:                        0.
% 2.28/0.96  smt_fast_solver_time:                   0.
% 2.28/0.96  prop_fast_solver_time:                  0.
% 2.28/0.96  prop_unsat_core_time:                   0.
% 2.28/0.96  
% 2.28/0.96  ------ QBF
% 2.28/0.96  
% 2.28/0.96  qbf_q_res:                              0
% 2.28/0.96  qbf_num_tautologies:                    0
% 2.28/0.96  qbf_prep_cycles:                        0
% 2.28/0.96  
% 2.28/0.96  ------ BMC1
% 2.28/0.96  
% 2.28/0.96  bmc1_current_bound:                     -1
% 2.28/0.96  bmc1_last_solved_bound:                 -1
% 2.28/0.96  bmc1_unsat_core_size:                   -1
% 2.28/0.96  bmc1_unsat_core_parents_size:           -1
% 2.28/0.96  bmc1_merge_next_fun:                    0
% 2.28/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.28/0.96  
% 2.28/0.96  ------ Instantiation
% 2.28/0.96  
% 2.28/0.96  inst_num_of_clauses:                    656
% 2.28/0.96  inst_num_in_passive:                    308
% 2.28/0.96  inst_num_in_active:                     240
% 2.28/0.96  inst_num_in_unprocessed:                108
% 2.28/0.96  inst_num_of_loops:                      240
% 2.28/0.96  inst_num_of_learning_restarts:          0
% 2.28/0.96  inst_num_moves_active_passive:          0
% 2.28/0.96  inst_lit_activity:                      0
% 2.28/0.96  inst_lit_activity_moves:                0
% 2.28/0.96  inst_num_tautologies:                   0
% 2.28/0.96  inst_num_prop_implied:                  0
% 2.28/0.96  inst_num_existing_simplified:           0
% 2.28/0.96  inst_num_eq_res_simplified:             0
% 2.28/0.96  inst_num_child_elim:                    0
% 2.28/0.96  inst_num_of_dismatching_blockings:      0
% 2.28/0.96  inst_num_of_non_proper_insts:           606
% 2.28/0.96  inst_num_of_duplicates:                 0
% 2.28/0.96  inst_inst_num_from_inst_to_res:         0
% 2.28/0.96  inst_dismatching_checking_time:         0.
% 2.28/0.96  
% 2.28/0.96  ------ Resolution
% 2.28/0.96  
% 2.28/0.96  res_num_of_clauses:                     0
% 2.28/0.96  res_num_in_passive:                     0
% 2.28/0.96  res_num_in_active:                      0
% 2.28/0.96  res_num_of_loops:                       91
% 2.28/0.96  res_forward_subset_subsumed:            4
% 2.28/0.96  res_backward_subset_subsumed:           0
% 2.28/0.96  res_forward_subsumed:                   0
% 2.28/0.96  res_backward_subsumed:                  0
% 2.28/0.96  res_forward_subsumption_resolution:     0
% 2.28/0.96  res_backward_subsumption_resolution:    0
% 2.28/0.96  res_clause_to_clause_subsumption:       133
% 2.28/0.96  res_orphan_elimination:                 0
% 2.28/0.96  res_tautology_del:                      1
% 2.28/0.96  res_num_eq_res_simplified:              0
% 2.28/0.96  res_num_sel_changes:                    0
% 2.28/0.96  res_moves_from_active_to_pass:          0
% 2.28/0.96  
% 2.28/0.96  ------ Superposition
% 2.28/0.96  
% 2.28/0.96  sup_time_total:                         0.
% 2.28/0.96  sup_time_generating:                    0.
% 2.28/0.96  sup_time_sim_full:                      0.
% 2.28/0.96  sup_time_sim_immed:                     0.
% 2.28/0.96  
% 2.28/0.96  sup_num_of_clauses:                     103
% 2.28/0.96  sup_num_in_active:                      41
% 2.28/0.96  sup_num_in_passive:                     62
% 2.28/0.96  sup_num_of_loops:                       47
% 2.28/0.96  sup_fw_superposition:                   86
% 2.28/0.96  sup_bw_superposition:                   3
% 2.28/0.96  sup_immediate_simplified:               7
% 2.28/0.96  sup_given_eliminated:                   0
% 2.28/0.96  comparisons_done:                       0
% 2.28/0.96  comparisons_avoided:                    95
% 2.28/0.96  
% 2.28/0.96  ------ Simplifications
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  sim_fw_subset_subsumed:                 1
% 2.28/0.96  sim_bw_subset_subsumed:                 0
% 2.28/0.96  sim_fw_subsumed:                        0
% 2.28/0.96  sim_bw_subsumed:                        0
% 2.28/0.96  sim_fw_subsumption_res:                 4
% 2.28/0.96  sim_bw_subsumption_res:                 0
% 2.28/0.96  sim_tautology_del:                      0
% 2.28/0.96  sim_eq_tautology_del:                   5
% 2.28/0.96  sim_eq_res_simp:                        3
% 2.28/0.96  sim_fw_demodulated:                     2
% 2.28/0.96  sim_bw_demodulated:                     7
% 2.28/0.96  sim_light_normalised:                   5
% 2.28/0.96  sim_joinable_taut:                      0
% 2.28/0.96  sim_joinable_simp:                      0
% 2.28/0.96  sim_ac_normalised:                      0
% 2.28/0.96  sim_smt_subsumption:                    0
% 2.28/0.96  
%------------------------------------------------------------------------------
