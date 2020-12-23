%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0887+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:20 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 192 expanded)
%              Number of clauses        :   41 (  52 expanded)
%              Number of leaves         :   15 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  452 (1266 expanded)
%              Number of equality atoms :  363 (1077 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                | k6_mcart_1(X0,X1,X2,X3) != X5
                | k5_mcart_1(X0,X1,X2,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
     => ( ( k7_mcart_1(X0,X1,X2,X3) != sK15
          | k6_mcart_1(X0,X1,X2,X3) != sK14
          | k5_mcart_1(X0,X1,X2,X3) != sK13 )
        & k3_mcart_1(sK13,sK14,sK15) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                | k6_mcart_1(X0,X1,X2,X3) != X5
                | k5_mcart_1(X0,X1,X2,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ? [X6,X5,X4] :
            ( ( k7_mcart_1(X0,X1,X2,sK12) != X6
              | k6_mcart_1(X0,X1,X2,sK12) != X5
              | k5_mcart_1(X0,X1,X2,sK12) != X4 )
            & k3_mcart_1(X4,X5,X6) = sK12 )
        & m1_subset_1(sK12,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                  | k6_mcart_1(X0,X1,X2,X3) != X5
                  | k5_mcart_1(X0,X1,X2,X3) != X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ? [X6,X5,X4] :
              ( ( k7_mcart_1(sK9,sK10,sK11,X3) != X6
                | k6_mcart_1(sK9,sK10,sK11,X3) != X5
                | k5_mcart_1(sK9,sK10,sK11,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK9,sK10,sK11)) )
      & k1_xboole_0 != sK11
      & k1_xboole_0 != sK10
      & k1_xboole_0 != sK9 ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( k7_mcart_1(sK9,sK10,sK11,sK12) != sK15
      | k6_mcart_1(sK9,sK10,sK11,sK12) != sK14
      | k5_mcart_1(sK9,sK10,sK11,sK12) != sK13 )
    & k3_mcart_1(sK13,sK14,sK15) = sK12
    & m1_subset_1(sK12,k3_zfmisc_1(sK9,sK10,sK11))
    & k1_xboole_0 != sK11
    & k1_xboole_0 != sK10
    & k1_xboole_0 != sK9 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13,sK14,sK15])],[f15,f30,f29,f28])).

fof(f47,plain,(
    m1_subset_1(sK12,k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    k3_mcart_1(sK13,sK14,sK15) = sK12 ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k5_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X5 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k5_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X5
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X5
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X5
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK0(X3,X4) != X4
        & k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK0(X3,X4) != X4
                    & k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f32,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X8
      | k3_mcart_1(X8,X9,X10) != X3
      | k5_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X8
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X8
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( k6_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X6 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k6_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X6
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X6
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X6
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK4(X3,X4) != X4
        & k3_mcart_1(sK3(X3,X4),sK4(X3,X4),sK5(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK4(X3,X4) != X4
                    & k3_mcart_1(sK3(X3,X4),sK4(X3,X4),sK5(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f22])).

fof(f35,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X9
      | k3_mcart_1(X8,X9,X10) != X3
      | k6_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X9
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f35])).

fof(f53,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9
      | ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ( k7_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X7 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X7
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X7
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X7
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X7
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X7
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK8(X3,X4) != X4
        & k3_mcart_1(sK6(X3,X4),sK7(X3,X4),sK8(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK8(X3,X4) != X4
                    & k3_mcart_1(sK6(X3,X4),sK7(X3,X4),sK8(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f26])).

fof(f38,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X10
      | k3_mcart_1(X8,X9,X10) != X3
      | k7_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X10
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f38])).

fof(f55,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,
    ( k7_mcart_1(sK9,sK10,sK11,sK12) != sK15
    | k6_mcart_1(sK9,sK10,sK11,sK12) != sK14
    | k5_mcart_1(sK9,sK10,sK11,sK12) != sK13 ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK12,k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_376,plain,
    ( m1_subset_1(sK12,k3_zfmisc_1(sK9,sK10,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( k3_mcart_1(sK13,sK14,sK15) = sK12 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2,plain,
    ( ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X0)
    | ~ m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
    | k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_386,plain,
    ( k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X0) != iProver_top
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_379,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_517,plain,
    ( k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_386,c_379])).

cnf(c_3443,plain,
    ( k5_mcart_1(X0,X1,X2,k3_mcart_1(sK13,sK14,sK15)) = sK13
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK12,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_517])).

cnf(c_3444,plain,
    ( k5_mcart_1(X0,X1,X2,sK12) = sK13
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK12,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3443,c_13])).

cnf(c_3452,plain,
    ( k5_mcart_1(sK9,sK10,sK11,sK12) = sK13
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_376,c_3444])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X1)
    | ~ m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
    | k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_383,plain,
    ( k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X1) != iProver_top
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_378,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_491,plain,
    ( k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_383,c_378])).

cnf(c_3048,plain,
    ( k6_mcart_1(X0,X1,X2,k3_mcart_1(sK13,sK14,sK15)) = sK14
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK12,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_491])).

cnf(c_3049,plain,
    ( k6_mcart_1(X0,X1,X2,sK12) = sK14
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK12,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3048,c_13])).

cnf(c_3057,plain,
    ( k6_mcart_1(sK9,sK10,sK11,sK12) = sK14
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_376,c_3049])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X2)
    | ~ m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
    | k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_380,plain,
    ( k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X2) != iProver_top
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_377,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_465,plain,
    ( k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_380,c_377])).

cnf(c_2446,plain,
    ( k7_mcart_1(X0,X1,X2,k3_mcart_1(sK13,sK14,sK15)) = sK15
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK12,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_465])).

cnf(c_2447,plain,
    ( k7_mcart_1(X0,X1,X2,sK12) = sK15
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK12,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2446,c_13])).

cnf(c_2505,plain,
    ( k7_mcart_1(sK9,sK10,sK11,sK12) = sK15
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_376,c_2447])).

cnf(c_160,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_570,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_571,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_568,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_569,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_566,plain,
    ( sK11 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_567,plain,
    ( sK11 != k1_xboole_0
    | k1_xboole_0 = sK11
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_159,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_174,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_12,negated_conjecture,
    ( k7_mcart_1(sK9,sK10,sK11,sK12) != sK15
    | k6_mcart_1(sK9,sK10,sK11,sK12) != sK14
    | k5_mcart_1(sK9,sK10,sK11,sK12) != sK13 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3452,c_3057,c_2505,c_571,c_569,c_567,c_174,c_12,c_15,c_16,c_17])).


%------------------------------------------------------------------------------
