%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0888+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 364 expanded)
%              Number of leaves         :   16 ( 143 expanded)
%              Depth                    :   15
%              Number of atoms          :  364 (1904 expanded)
%              Number of equality atoms :  257 (1377 expanded)
%              Maximal formula depth    :   16 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f41,plain,(
    sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,X3),k6_mcart_1(sK0,sK1,sK2,X3),k7_mcart_1(sK0,sK1,sK2,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,X3),k6_mcart_1(sK0,sK1,sK2,X3),k7_mcart_1(sK0,sK1,sK2,X3)) != X3
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f97,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f87,f94])).

fof(f94,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = sK4(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | sK4(sK0,sK1,sK2,sK3) = k5_mcart_1(X0,X1,X2,sK3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f80,f77])).

fof(f77,plain,(
    sK3 = k3_mcart_1(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f70,f74])).

fof(f74,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = sK6(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | sK6(sK0,sK1,sK2,sK3) = k7_mcart_1(X0,X1,X2,sK3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f71,f70])).

fof(f71,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f59,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f59,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X10
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X10
      | k3_mcart_1(X8,X9,X10) != X3
      | k7_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK9(X3,X4) != X4
                    & k3_mcart_1(sK7(X3,X4),sK8(X3,X4),sK9(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f26,f27])).

fof(f27,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X7
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK9(X3,X4) != X4
        & k3_mcart_1(sK7(X3,X4),sK8(X3,X4),sK9(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_mcart_1)).

fof(f70,plain,(
    sK3 = k3_mcart_1(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3),sK6(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK6(X0,X1,X2,X3),X2)
            & m1_subset_1(sK5(X0,X1,X2,X3),X1)
            & m1_subset_1(sK4(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f11,f23,f22,f21])).

fof(f21,plain,(
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
                ( k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK5(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK6(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f80,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X8
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f63,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f63,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X8
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X8
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X8
      | k3_mcart_1(X8,X9,X10) != X3
      | k5_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK13(X3,X4) != X4
                    & k3_mcart_1(sK13(X3,X4),sK14(X3,X4),sK15(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f34,f35])).

fof(f35,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X5
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK13(X3,X4) != X4
        & k3_mcart_1(sK13(X3,X4),sK14(X3,X4),sK15(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_mcart_1)).

fof(f40,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    sK3 = k3_mcart_1(sK4(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f77,f84])).

fof(f84,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = sK5(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | sK5(sK0,sK1,sK2,sK3) = k6_mcart_1(X0,X1,X2,sK3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f73,f70])).

fof(f73,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f61,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f61,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9
      | ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X9
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X9
      | k3_mcart_1(X8,X9,X10) != X3
      | k6_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK11(X3,X4) != X4
                    & k3_mcart_1(sK10(X3,X4),sK11(X3,X4),sK12(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f30,f31])).

fof(f31,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X6
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK11(X3,X4) != X4
        & k3_mcart_1(sK10(X3,X4),sK11(X3,X4),sK12(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_mcart_1)).

%------------------------------------------------------------------------------
