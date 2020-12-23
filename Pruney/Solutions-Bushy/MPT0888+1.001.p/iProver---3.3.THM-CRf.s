%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0888+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:20 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  133 (1791 expanded)
%              Number of clauses        :   77 ( 692 expanded)
%              Number of leaves         :   18 ( 592 expanded)
%              Depth                    :   26
%              Number of atoms          :  595 (7850 expanded)
%              Number of equality atoms :  472 (6103 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   11 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( k3_mcart_1(k5_mcart_1(X0,X1,X2,sK15),k6_mcart_1(X0,X1,X2,sK15),k7_mcart_1(X0,X1,X2,sK15)) != sK15
        & m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,X3),k6_mcart_1(sK12,sK13,sK14,X3),k7_mcart_1(sK12,sK13,sK14,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(sK12,sK13,sK14)) )
      & k1_xboole_0 != sK14
      & k1_xboole_0 != sK13
      & k1_xboole_0 != sK12 ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,sK15),k6_mcart_1(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15)) != sK15
    & m1_subset_1(sK15,k3_zfmisc_1(sK12,sK13,sK14))
    & k1_xboole_0 != sK14
    & k1_xboole_0 != sK13
    & k1_xboole_0 != sK12 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14,sK15])],[f17,f35,f34])).

fof(f56,plain,(
    m1_subset_1(sK15,k3_zfmisc_1(sK12,sK13,sK14)) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X4,X5,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(X4,X5,X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(X4,X5,sK11(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK11(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(X4,X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(X4,sK10(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK10(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK9(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK9(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK11(X0,X1,X2,X3),X2)
            & m1_subset_1(sK10(X0,X1,X2,X3),X1)
            & m1_subset_1(sK9(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f16,f32,f31,f30])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f10,plain,(
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

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X5
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK0(X3,X4) != X4
        & k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    k1_xboole_0 != sK12 ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    k1_xboole_0 != sK13 ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    k1_xboole_0 != sK14 ),
    inference(cnf_transformation,[],[f36])).

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

fof(f12,plain,(
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

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X7
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK8(X3,X4) != X4
        & k3_mcart_1(sK6(X3,X4),sK7(X3,X4),sK8(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f27,f28])).

fof(f43,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X10
      | k3_mcart_1(X8,X9,X10) != X3
      | k7_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X10
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f63,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f11,plain,(
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

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X6
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK4(X3,X4) != X4
        & k3_mcart_1(sK3(X3,X4),sK4(X3,X4),sK5(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f24])).

fof(f40,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X9
      | k3_mcart_1(X8,X9,X10) != X3
      | k6_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X9
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f61,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9
      | ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f60])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X8
      | k3_mcart_1(X8,X9,X10) != X3
      | k5_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X8
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f37])).

fof(f59,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X8
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f58])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,sK15),k6_mcart_1(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15)) != sK15 ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK15,k3_zfmisc_1(sK12,sK13,sK14)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_475,plain,
    ( m1_subset_1(sK15,k3_zfmisc_1(sK12,sK13,sK14)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(sK9(X1,X2,X3,X0),X1)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_476,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X1,X0,X2)) != iProver_top
    | m1_subset_1(sK9(X1,X0,X2,X3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k3_zfmisc_1(X1,X3,X4))
    | k5_mcart_1(X1,X3,X4,X2) = X0
    | k3_mcart_1(sK0(X2,X0),sK1(X2,X0),sK2(X2,X0)) = X2
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_490,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k3_mcart_1(sK0(X3,X4),sK1(X3,X4),sK2(X3,X4)) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2455,plain,
    ( k5_mcart_1(sK12,sK13,sK14,sK15) = X0
    | k3_mcart_1(sK0(sK15,X0),sK1(sK15,X0),sK2(sK15,X0)) = sK15
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0
    | sK12 = k1_xboole_0
    | m1_subset_1(X0,sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_475,c_490])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK12 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK13 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK14 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_202,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_217,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_203,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_711,plain,
    ( sK14 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK14 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_712,plain,
    ( sK14 != k1_xboole_0
    | k1_xboole_0 = sK14
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_713,plain,
    ( sK13 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK13 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_714,plain,
    ( sK13 != k1_xboole_0
    | k1_xboole_0 = sK13
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_715,plain,
    ( sK12 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK12 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_716,plain,
    ( sK12 != k1_xboole_0
    | k1_xboole_0 = sK12
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_2769,plain,
    ( k3_mcart_1(sK0(sK15,X0),sK1(sK15,X0),sK2(sK15,X0)) = sK15
    | k5_mcart_1(sK12,sK13,sK14,sK15) = X0
    | m1_subset_1(X0,sK12) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2455,c_20,c_19,c_18,c_217,c_712,c_714,c_716])).

cnf(c_2770,plain,
    ( k5_mcart_1(sK12,sK13,sK14,sK15) = X0
    | k3_mcart_1(sK0(sK15,X0),sK1(sK15,X0),sK2(sK15,X0)) = sK15
    | m1_subset_1(X0,sK12) != iProver_top ),
    inference(renaming,[status(thm)],[c_2769])).

cnf(c_2781,plain,
    ( sK9(sK12,X0,X1,X2) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k3_mcart_1(sK0(sK15,sK9(sK12,X0,X1,X2)),sK1(sK15,sK9(sK12,X0,X1,X2)),sK2(sK15,sK9(sK12,X0,X1,X2))) = sK15
    | sK12 = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X2,k3_zfmisc_1(sK12,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_2770])).

cnf(c_4662,plain,
    ( k3_mcart_1(sK0(sK15,sK9(sK12,X0,X1,X2)),sK1(sK15,sK9(sK12,X0,X1,X2)),sK2(sK15,sK9(sK12,X0,X1,X2))) = sK15
    | sK9(sK12,X0,X1,X2) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X2,k3_zfmisc_1(sK12,X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2781,c_20,c_217,c_716])).

cnf(c_4663,plain,
    ( sK9(sK12,X0,X1,X2) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k3_mcart_1(sK0(sK15,sK9(sK12,X0,X1,X2)),sK1(sK15,sK9(sK12,X0,X1,X2)),sK2(sK15,sK9(sK12,X0,X1,X2))) = sK15
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X2,k3_zfmisc_1(sK12,X0,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4662])).

cnf(c_4674,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15))) = sK15
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_4663])).

cnf(c_5351,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15))) = sK15 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4674,c_19,c_18,c_217,c_712,c_714])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X2)
    | ~ m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
    | k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_483,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_480,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_602,plain,
    ( k7_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X5
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_483,c_480])).

cnf(c_5357,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k7_mcart_1(X0,X1,X2,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK2(sK15,sK9(sK12,sK13,sK14,sK15))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5351,c_602])).

cnf(c_12458,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k7_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK2(sK15,sK9(sK12,sK13,sK14,sK15))
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_5357])).

cnf(c_12559,plain,
    ( k7_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK2(sK15,sK9(sK12,sK13,sK14,sK15))
    | sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12458,c_20,c_19,c_18,c_217,c_712,c_714,c_716])).

cnf(c_12560,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k7_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK2(sK15,sK9(sK12,sK13,sK14,sK15)) ),
    inference(renaming,[status(thm)],[c_12559])).

cnf(c_12563,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | sK2(sK15,sK9(sK12,sK13,sK14,sK15)) = k7_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(superposition,[status(thm)],[c_5351,c_12560])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X1)
    | ~ m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
    | k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_486,plain,
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
    inference(cnf_transformation,[],[f47])).

cnf(c_481,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_628,plain,
    ( k6_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_486,c_481])).

cnf(c_5356,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k6_mcart_1(X0,X1,X2,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK1(sK15,sK9(sK12,sK13,sK14,sK15))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5351,c_628])).

cnf(c_11606,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k6_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK1(sK15,sK9(sK12,sK13,sK14,sK15))
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_5356])).

cnf(c_11847,plain,
    ( k6_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK1(sK15,sK9(sK12,sK13,sK14,sK15))
    | sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11606,c_20,c_19,c_18,c_217,c_712,c_714,c_716])).

cnf(c_11848,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k6_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK1(sK15,sK9(sK12,sK13,sK14,sK15)) ),
    inference(renaming,[status(thm)],[c_11847])).

cnf(c_11851,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | sK1(sK15,sK9(sK12,sK13,sK14,sK15)) = k6_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(superposition,[status(thm)],[c_5351,c_11848])).

cnf(c_2,plain,
    ( ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)),X0)
    | ~ m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
    | k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_489,plain,
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
    inference(cnf_transformation,[],[f46])).

cnf(c_482,plain,
    ( m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_654,plain,
    ( k5_mcart_1(X0,X1,X2,k3_mcart_1(X3,X4,X5)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_489,c_482])).

cnf(c_5355,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k5_mcart_1(X0,X1,X2,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK0(sK15,sK9(sK12,sK13,sK14,sK15))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5351,c_654])).

cnf(c_11456,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k5_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK0(sK15,sK9(sK12,sK13,sK14,sK15))
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_5355])).

cnf(c_11468,plain,
    ( k5_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK0(sK15,sK9(sK12,sK13,sK14,sK15))
    | sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11456,c_20,c_19,c_18,c_217,c_712,c_714,c_716])).

cnf(c_11469,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k5_mcart_1(sK12,sK13,sK14,k3_mcart_1(sK0(sK15,sK9(sK12,sK13,sK14,sK15)),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15)))) = sK0(sK15,sK9(sK12,sK13,sK14,sK15)) ),
    inference(renaming,[status(thm)],[c_11468])).

cnf(c_11472,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | sK0(sK15,sK9(sK12,sK13,sK14,sK15)) = k5_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(superposition,[status(thm)],[c_5351,c_11469])).

cnf(c_11489,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,sK15),sK1(sK15,sK9(sK12,sK13,sK14,sK15)),sK2(sK15,sK9(sK12,sK13,sK14,sK15))) = sK15 ),
    inference(superposition,[status(thm)],[c_11472,c_5351])).

cnf(c_12071,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,sK15),k6_mcart_1(sK12,sK13,sK14,sK15),sK2(sK15,sK9(sK12,sK13,sK14,sK15))) = sK15 ),
    inference(superposition,[status(thm)],[c_11851,c_11489])).

cnf(c_14412,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15)
    | k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,sK15),k6_mcart_1(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15)) = sK15 ),
    inference(superposition,[status(thm)],[c_12563,c_12071])).

cnf(c_16,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,sK15),k6_mcart_1(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15)) != sK15 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14963,plain,
    ( sK9(sK12,sK13,sK14,sK15) = k5_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14412,c_16])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k3_mcart_1(sK9(X1,X2,X3,X0),sK10(X1,X2,X3,X0),sK11(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_479,plain,
    ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1322,plain,
    ( k3_mcart_1(sK9(sK12,sK13,sK14,sK15),sK10(sK12,sK13,sK14,sK15),sK11(sK12,sK13,sK14,sK15)) = sK15
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_479])).

cnf(c_1596,plain,
    ( k3_mcart_1(sK9(sK12,sK13,sK14,sK15),sK10(sK12,sK13,sK14,sK15),sK11(sK12,sK13,sK14,sK15)) = sK15 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1322,c_20,c_19,c_18,c_217,c_712,c_714,c_716])).

cnf(c_1769,plain,
    ( k7_mcart_1(X0,X1,X2,k3_mcart_1(sK9(sK12,sK13,sK14,sK15),sK10(sK12,sK13,sK14,sK15),sK11(sK12,sK13,sK14,sK15))) = sK11(sK12,sK13,sK14,sK15)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_602])).

cnf(c_1770,plain,
    ( k7_mcart_1(X0,X1,X2,sK15) = sK11(sK12,sK13,sK14,sK15)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1769,c_1596])).

cnf(c_1778,plain,
    ( sK11(sK12,sK13,sK14,sK15) = k7_mcart_1(sK12,sK13,sK14,sK15)
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_1770])).

cnf(c_1943,plain,
    ( sK11(sK12,sK13,sK14,sK15) = k7_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1778,c_20,c_19,c_18,c_217,c_712,c_714,c_716])).

cnf(c_1947,plain,
    ( k3_mcart_1(sK9(sK12,sK13,sK14,sK15),sK10(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15)) = sK15 ),
    inference(demodulation,[status(thm)],[c_1943,c_1596])).

cnf(c_2124,plain,
    ( k6_mcart_1(X0,X1,X2,k3_mcart_1(sK9(sK12,sK13,sK14,sK15),sK10(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15))) = sK10(sK12,sK13,sK14,sK15)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1947,c_628])).

cnf(c_2125,plain,
    ( k6_mcart_1(X0,X1,X2,sK15) = sK10(sK12,sK13,sK14,sK15)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK15,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2124,c_1947])).

cnf(c_12592,plain,
    ( sK10(sK12,sK13,sK14,sK15) = k6_mcart_1(sK12,sK13,sK14,sK15)
    | sK14 = k1_xboole_0
    | sK13 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_2125])).

cnf(c_12693,plain,
    ( sK10(sK12,sK13,sK14,sK15) = k6_mcart_1(sK12,sK13,sK14,sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12592,c_20,c_19,c_18,c_217,c_712,c_714,c_716])).

cnf(c_12697,plain,
    ( k3_mcart_1(sK9(sK12,sK13,sK14,sK15),k6_mcart_1(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15)) = sK15 ),
    inference(demodulation,[status(thm)],[c_12693,c_1947])).

cnf(c_14966,plain,
    ( k3_mcart_1(k5_mcart_1(sK12,sK13,sK14,sK15),k6_mcart_1(sK12,sK13,sK14,sK15),k7_mcart_1(sK12,sK13,sK14,sK15)) = sK15 ),
    inference(demodulation,[status(thm)],[c_14963,c_12697])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14966,c_16])).


%------------------------------------------------------------------------------
