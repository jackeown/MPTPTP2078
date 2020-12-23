%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0900+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:22 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 920 expanded)
%              Number of clauses        :   63 ( 338 expanded)
%              Number of leaves         :   22 ( 320 expanded)
%              Depth                    :   19
%              Number of atoms          :  689 (4542 expanded)
%              Number of equality atoms :  537 (3550 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,sK24),k9_mcart_1(X0,X1,X2,X3,sK24),k10_mcart_1(X0,X1,X2,X3,sK24),k11_mcart_1(X0,X1,X2,X3,sK24)) != sK24
        & m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(sK20,sK21,sK22,sK23,X4),k9_mcart_1(sK20,sK21,sK22,sK23,X4),k10_mcart_1(sK20,sK21,sK22,sK23,X4),k11_mcart_1(sK20,sK21,sK22,sK23,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(sK20,sK21,sK22,sK23)) )
      & k1_xboole_0 != sK23
      & k1_xboole_0 != sK22
      & k1_xboole_0 != sK21
      & k1_xboole_0 != sK20 ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k4_mcart_1(k8_mcart_1(sK20,sK21,sK22,sK23,sK24),k9_mcart_1(sK20,sK21,sK22,sK23,sK24),k10_mcart_1(sK20,sK21,sK22,sK23,sK24),k11_mcart_1(sK20,sK21,sK22,sK23,sK24)) != sK24
    & m1_subset_1(sK24,k4_zfmisc_1(sK20,sK21,sK22,sK23))
    & k1_xboole_0 != sK23
    & k1_xboole_0 != sK22
    & k1_xboole_0 != sK21
    & k1_xboole_0 != sK20 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21,sK22,sK23,sK24])],[f21,f44,f43])).

fof(f71,plain,(
    m1_subset_1(sK24,k4_zfmisc_1(sK20,sK21,sK22,sK23)) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(X5,X6,X7,X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(X5,X6,X7,sK19(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK19(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(X5,X6,X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(X5,X6,sK18(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK18(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(X5,sK17(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK17(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK16(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK16(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK16(X0,X1,X2,X3,X4),sK17(X0,X1,X2,X3,X4),sK18(X0,X1,X2,X3,X4),sK19(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK19(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK18(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK17(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK16(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18,sK19])],[f20,f41,f40,f39,f38])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK16(X0,X1,X2,X3,X4),sK17(X0,X1,X2,X3,X4),sK18(X0,X1,X2,X3,X4),sK19(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    k1_xboole_0 != sK20 ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    k1_xboole_0 != sK21 ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    k1_xboole_0 != sK22 ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    k1_xboole_0 != sK23 ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK2(X4,X5) != X5
        & k4_mcart_1(sK0(X4,X5),sK1(X4,X5),sK2(X4,X5),sK3(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f46])).

fof(f74,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f73])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X9
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK7(X4,X5) != X5
        & k4_mcart_1(sK4(X4,X5),sK5(X4,X5),sK6(X4,X5),sK7(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f28])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f49])).

fof(f76,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f75])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK8(X4,X5) != X5
        & k4_mcart_1(sK8(X4,X5),sK9(X4,X5),sK10(X4,X5),sK11(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f31,f32])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f52])).

fof(f78,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f77])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X7
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK13(X4,X5) != X5
        & k4_mcart_1(sK12(X4,X5),sK13(X4,X5),sK14(X4,X5),sK15(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14,sK15])],[f35,f36])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f55])).

fof(f80,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f79])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    k4_mcart_1(k8_mcart_1(sK20,sK21,sK22,sK23,sK24),k9_mcart_1(sK20,sK21,sK22,sK23,sK24),k10_mcart_1(sK20,sK21,sK22,sK23,sK24),k11_mcart_1(sK20,sK21,sK22,sK23,sK24)) != sK24 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK24,k4_zfmisc_1(sK20,sK21,sK22,sK23)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_607,plain,
    ( m1_subset_1(sK24,k4_zfmisc_1(sK20,sK21,sK22,sK23)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k4_mcart_1(sK16(X1,X2,X3,X4,X0),sK17(X1,X2,X3,X4,X0),sK18(X1,X2,X3,X4,X0),sK19(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_612,plain,
    ( k4_mcart_1(sK16(X0,X1,X2,X3,X4),sK17(X0,X1,X2,X3,X4),sK18(X0,X1,X2,X3,X4),sK19(X0,X1,X2,X3,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2640,plain,
    ( k4_mcart_1(sK16(sK20,sK21,sK22,sK23,sK24),sK17(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24)) = sK24
    | sK23 = k1_xboole_0
    | sK22 = k1_xboole_0
    | sK21 = k1_xboole_0
    | sK20 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_612])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK20 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK21 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK22 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK23 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_260,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_277,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_261,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_948,plain,
    ( sK23 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK23 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_949,plain,
    ( sK23 != k1_xboole_0
    | k1_xboole_0 = sK23
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_950,plain,
    ( sK22 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK22 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_951,plain,
    ( sK22 != k1_xboole_0
    | k1_xboole_0 = sK22
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_952,plain,
    ( sK21 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK21 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_953,plain,
    ( sK21 != k1_xboole_0
    | k1_xboole_0 = sK21
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_954,plain,
    ( sK20 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK20 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_955,plain,
    ( sK20 != k1_xboole_0
    | k1_xboole_0 = sK20
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_4053,plain,
    ( k4_mcart_1(sK16(sK20,sK21,sK22,sK23,sK24),sK17(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24)) = sK24 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2640,c_26,c_25,c_24,c_23,c_277,c_949,c_951,c_953,c_955])).

cnf(c_2,plain,
    ( ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X2)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_626,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_616,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_894,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X6
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_626,c_616])).

cnf(c_4056,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK16(sK20,sK21,sK22,sK23,sK24),sK17(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24))) = sK18(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_894])).

cnf(c_4105,plain,
    ( k10_mcart_1(X0,X1,X2,X3,sK24) = sK18(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4056,c_4053])).

cnf(c_6177,plain,
    ( sK18(sK20,sK21,sK22,sK23,sK24) = k10_mcart_1(sK20,sK21,sK22,sK23,sK24)
    | sK23 = k1_xboole_0
    | sK22 = k1_xboole_0
    | sK21 = k1_xboole_0
    | sK20 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_4105])).

cnf(c_6178,plain,
    ( sK18(sK20,sK21,sK22,sK23,sK24) = k10_mcart_1(sK20,sK21,sK22,sK23,sK24) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6177,c_26,c_25,c_24,c_23,c_277,c_949,c_951,c_953,c_955])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X3)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_623,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_615,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_880,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X7
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_623,c_615])).

cnf(c_4057,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK16(sK20,sK21,sK22,sK23,sK24),sK17(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24))) = sK19(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_880])).

cnf(c_4092,plain,
    ( k11_mcart_1(X0,X1,X2,X3,sK24) = sK19(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4057,c_4053])).

cnf(c_6087,plain,
    ( sK19(sK20,sK21,sK22,sK23,sK24) = k11_mcart_1(sK20,sK21,sK22,sK23,sK24)
    | sK23 = k1_xboole_0
    | sK22 = k1_xboole_0
    | sK21 = k1_xboole_0
    | sK20 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_4092])).

cnf(c_6088,plain,
    ( sK19(sK20,sK21,sK22,sK23,sK24) = k11_mcart_1(sK20,sK21,sK22,sK23,sK24) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6087,c_26,c_25,c_24,c_23,c_277,c_949,c_951,c_953,c_955])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X0)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_620,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_614,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_866,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_620,c_614])).

cnf(c_4058,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK16(sK20,sK21,sK22,sK23,sK24),sK17(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24))) = sK16(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_866])).

cnf(c_4079,plain,
    ( k8_mcart_1(X0,X1,X2,X3,sK24) = sK16(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4058,c_4053])).

cnf(c_5461,plain,
    ( sK16(sK20,sK21,sK22,sK23,sK24) = k8_mcart_1(sK20,sK21,sK22,sK23,sK24)
    | sK23 = k1_xboole_0
    | sK22 = k1_xboole_0
    | sK21 = k1_xboole_0
    | sK20 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_4079])).

cnf(c_5665,plain,
    ( sK16(sK20,sK21,sK22,sK23,sK24) = k8_mcart_1(sK20,sK21,sK22,sK23,sK24) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5461,c_26,c_25,c_24,c_23,c_277,c_949,c_951,c_953,c_955])).

cnf(c_11,plain,
    ( ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)),X1)
    | ~ m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
    | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_617,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_613,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_852,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X4,X5,X6,X7)) = X5
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k4_mcart_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_617,c_613])).

cnf(c_4059,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK16(sK20,sK21,sK22,sK23,sK24),sK17(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24))) = sK17(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_852])).

cnf(c_4066,plain,
    ( k9_mcart_1(X0,X1,X2,X3,sK24) = sK17(sK20,sK21,sK22,sK23,sK24)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK24,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4059,c_4053])).

cnf(c_4905,plain,
    ( sK17(sK20,sK21,sK22,sK23,sK24) = k9_mcart_1(sK20,sK21,sK22,sK23,sK24)
    | sK23 = k1_xboole_0
    | sK22 = k1_xboole_0
    | sK21 = k1_xboole_0
    | sK20 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_4066])).

cnf(c_4906,plain,
    ( sK17(sK20,sK21,sK22,sK23,sK24) = k9_mcart_1(sK20,sK21,sK22,sK23,sK24) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4905,c_26,c_25,c_24,c_23,c_277,c_949,c_951,c_953,c_955])).

cnf(c_4910,plain,
    ( k4_mcart_1(sK16(sK20,sK21,sK22,sK23,sK24),k9_mcart_1(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24)) = sK24 ),
    inference(demodulation,[status(thm)],[c_4906,c_4053])).

cnf(c_5669,plain,
    ( k4_mcart_1(k8_mcart_1(sK20,sK21,sK22,sK23,sK24),k9_mcart_1(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),sK19(sK20,sK21,sK22,sK23,sK24)) = sK24 ),
    inference(demodulation,[status(thm)],[c_5665,c_4910])).

cnf(c_6092,plain,
    ( k4_mcart_1(k8_mcart_1(sK20,sK21,sK22,sK23,sK24),k9_mcart_1(sK20,sK21,sK22,sK23,sK24),sK18(sK20,sK21,sK22,sK23,sK24),k11_mcart_1(sK20,sK21,sK22,sK23,sK24)) = sK24 ),
    inference(demodulation,[status(thm)],[c_6088,c_5669])).

cnf(c_6182,plain,
    ( k4_mcart_1(k8_mcart_1(sK20,sK21,sK22,sK23,sK24),k9_mcart_1(sK20,sK21,sK22,sK23,sK24),k10_mcart_1(sK20,sK21,sK22,sK23,sK24),k11_mcart_1(sK20,sK21,sK22,sK23,sK24)) = sK24 ),
    inference(demodulation,[status(thm)],[c_6178,c_6092])).

cnf(c_21,negated_conjecture,
    ( k4_mcart_1(k8_mcart_1(sK20,sK21,sK22,sK23,sK24),k9_mcart_1(sK20,sK21,sK22,sK23,sK24),k10_mcart_1(sK20,sK21,sK22,sK23,sK24),k11_mcart_1(sK20,sK21,sK22,sK23,sK24)) != sK24 ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6182,c_21])).


%------------------------------------------------------------------------------
