%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:33 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 159 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   24
%              Number of atoms          :  351 (1304 expanded)
%              Number of equality atoms :  245 ( 787 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f25,f138])).

fof(f138,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f26,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f27,f95])).

fof(f95,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,
    ( sK3 != sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f85])).

fof(f85,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f57,f73])).

fof(f73,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f72,f23])).

fof(f23,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f72,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4) ),
    inference(resolution,[],[f55,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f55,plain,
    ( ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( ~ m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f45,f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),X2)
      | sK10(sK0,sK1,sK2,sK4) = k7_mcart_1(X0,X1,X2,sK4)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f38,f42])).

fof(f42,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f23,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK10(X0,X1,X2,X3),X2)
            & m1_subset_1(sK9(X0,X1,X2,X3),X1)
            & m1_subset_1(sK8(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f12,f21,f20,f19])).

fof(f19,plain,(
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
                ( k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK8(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK9(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK10(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f38,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X2)
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X10
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X10
      | k3_mcart_1(X8,X9,X10) != X3
      | k7_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k7_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK7(X3,X4) != X4
                    & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X10
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k7_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X7
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK7(X3,X4) != X4
        & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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

fof(f57,plain,
    ( sK3 = sK10(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( sK3 = sK10(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f53,f39])).

fof(f39,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK8(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | sK3 = sK10(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,
    ( sK3 = sK10(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK9(X0,X1,X2,X3),X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | sK3 = sK10(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,
    ( sK3 = sK10(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK10(X0,X1,X2,X3),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | sK3 = sK10(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( sK4 != sK4
    | sK3 = sK10(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f24,f42])).

fof(f24,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.26/0.53  % (25957)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.53  % (25962)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.53  % (25956)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.26/0.53  % (25954)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.53  % (25960)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.26/0.54  % (25969)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.26/0.54  % (25974)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.54  % (25961)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.26/0.54  % (25953)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.54  % (25966)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.54  % (25963)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.26/0.54  % (25972)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.26/0.54  % (25953)Refutation found. Thanks to Tanya!
% 1.26/0.54  % SZS status Theorem for theBenchmark
% 1.26/0.54  % SZS output start Proof for theBenchmark
% 1.26/0.54  fof(f144,plain,(
% 1.26/0.54    $false),
% 1.26/0.54    inference(trivial_inequality_removal,[],[f143])).
% 1.26/0.54  fof(f143,plain,(
% 1.26/0.54    k1_xboole_0 != k1_xboole_0),
% 1.26/0.54    inference(superposition,[],[f25,f138])).
% 1.26/0.54  fof(f138,plain,(
% 1.26/0.54    k1_xboole_0 = sK0),
% 1.26/0.54    inference(trivial_inequality_removal,[],[f121])).
% 1.26/0.54  fof(f121,plain,(
% 1.26/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(superposition,[],[f26,f119])).
% 1.26/0.54  fof(f119,plain,(
% 1.26/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(trivial_inequality_removal,[],[f99])).
% 1.26/0.54  fof(f99,plain,(
% 1.26/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(superposition,[],[f27,f95])).
% 1.26/0.54  fof(f95,plain,(
% 1.26/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(trivial_inequality_removal,[],[f93])).
% 1.26/0.54  fof(f93,plain,(
% 1.26/0.54    sK3 != sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(superposition,[],[f28,f85])).
% 1.26/0.54  fof(f85,plain,(
% 1.26/0.54    sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f78])).
% 1.26/0.54  fof(f78,plain,(
% 1.26/0.54    sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 1.26/0.54    inference(superposition,[],[f57,f73])).
% 1.26/0.54  fof(f73,plain,(
% 1.26/0.54    k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 1.26/0.54    inference(resolution,[],[f72,f23])).
% 1.26/0.54  fof(f23,plain,(
% 1.26/0.54    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  fof(f14,plain,(
% 1.26/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).
% 1.26/0.54  fof(f13,plain,(
% 1.26/0.54    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f9,plain,(
% 1.26/0.54    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.26/0.54    inference(flattening,[],[f8])).
% 1.26/0.54  fof(f8,plain,(
% 1.26/0.54    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.26/0.54    inference(ennf_transformation,[],[f7])).
% 1.26/0.54  fof(f7,negated_conjecture,(
% 1.26/0.54    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.26/0.54    inference(negated_conjecture,[],[f6])).
% 1.26/0.54  fof(f6,conjecture,(
% 1.26/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.26/0.54  fof(f72,plain,(
% 1.26/0.54    ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4)),
% 1.26/0.54    inference(resolution,[],[f55,f29])).
% 1.26/0.54  fof(f29,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f10])).
% 1.26/0.54  fof(f10,plain,(
% 1.26/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.26/0.54    inference(ennf_transformation,[],[f4])).
% 1.26/0.54  fof(f4,axiom,(
% 1.26/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 1.26/0.54  fof(f55,plain,(
% 1.26/0.54    ~m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) | k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f54])).
% 1.26/0.54  fof(f54,plain,(
% 1.26/0.54    ~m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) | k7_mcart_1(sK0,sK1,sK2,sK4) = sK10(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f45,f23])).
% 1.26/0.54  fof(f45,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2)) | ~m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),X2) | sK10(sK0,sK1,sK2,sK4) = k7_mcart_1(X0,X1,X2,sK4) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.26/0.54    inference(superposition,[],[f38,f42])).
% 1.26/0.54  fof(f42,plain,(
% 1.26/0.54    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f23,f36])).
% 1.26/0.54  fof(f36,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(cnf_transformation,[],[f22])).
% 1.26/0.54  fof(f22,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 & m1_subset_1(sK10(X0,X1,X2,X3),X2)) & m1_subset_1(sK9(X0,X1,X2,X3),X1)) & m1_subset_1(sK8(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f12,f21,f20,f19])).
% 1.26/0.54  fof(f19,plain,(
% 1.26/0.54    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8(X0,X1,X2,X3),X0)))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f20,plain,(
% 1.26/0.54    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK9(X0,X1,X2,X3),X1)))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f21,plain,(
% 1.26/0.54    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 & m1_subset_1(sK10(X0,X1,X2,X3),X2)))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f12,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.54    inference(ennf_transformation,[],[f5])).
% 1.26/0.54  fof(f5,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ( ! [X2,X0,X10,X8,X1,X9] : (~m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2)) | ~m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X2) | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X10 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(equality_resolution,[],[f37])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    ( ! [X4,X2,X0,X10,X8,X1,X9] : (X4 = X10 | k7_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4 | ~m1_subset_1(X4,X2) | ~m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(equality_resolution,[],[f30])).
% 1.26/0.54  fof(f30,plain,(
% 1.26/0.54    ( ! [X4,X2,X0,X10,X8,X3,X1,X9] : (X4 = X10 | k3_mcart_1(X8,X9,X10) != X3 | k7_mcart_1(X0,X1,X2,X3) != X4 | ~m1_subset_1(X4,X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(cnf_transformation,[],[f18])).
% 1.26/0.54  fof(f18,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k7_mcart_1(X0,X1,X2,X3) = X4 | (sK7(X3,X4) != X4 & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3)) & (! [X8,X9,X10] : (X4 = X10 | k3_mcart_1(X8,X9,X10) != X3) | k7_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X2)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f17])).
% 1.26/0.54  fof(f17,plain,(
% 1.26/0.54    ! [X4,X3] : (? [X5,X6,X7] : (X4 != X7 & k3_mcart_1(X5,X6,X7) = X3) => (sK7(X3,X4) != X4 & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f16,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k7_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X7 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X8,X9,X10] : (X4 = X10 | k3_mcart_1(X8,X9,X10) != X3) | k7_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X2)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.54    inference(rectify,[],[f15])).
% 1.26/0.54  fof(f15,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k7_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X7 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X5,X6,X7] : (X4 = X7 | k3_mcart_1(X5,X6,X7) != X3) | k7_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X2)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.54    inference(nnf_transformation,[],[f11])).
% 1.26/0.54  fof(f11,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((k7_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (X4 = X7 | k3_mcart_1(X5,X6,X7) != X3)) | ~m1_subset_1(X4,X2)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.54    inference(ennf_transformation,[],[f3])).
% 1.26/0.54  fof(f3,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ! [X4] : (m1_subset_1(X4,X2) => (k7_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (k3_mcart_1(X5,X6,X7) = X3 => X4 = X7)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_mcart_1)).
% 1.26/0.54  fof(f57,plain,(
% 1.26/0.54    sK3 = sK10(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f56])).
% 1.26/0.54  fof(f56,plain,(
% 1.26/0.54    sK3 = sK10(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f53,f39])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f23,f33])).
% 1.26/0.54  fof(f33,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK8(X0,X1,X2,X3),X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(cnf_transformation,[],[f22])).
% 1.26/0.54  fof(f53,plain,(
% 1.26/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | sK3 = sK10(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f52])).
% 1.26/0.54  fof(f52,plain,(
% 1.26/0.54    sK3 = sK10(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f51,f40])).
% 1.26/0.54  fof(f40,plain,(
% 1.26/0.54    m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f23,f34])).
% 1.26/0.54  fof(f34,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK9(X0,X1,X2,X3),X1) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(cnf_transformation,[],[f22])).
% 1.26/0.54  fof(f51,plain,(
% 1.26/0.54    ~m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | sK3 = sK10(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f50])).
% 1.26/0.54  fof(f50,plain,(
% 1.26/0.54    sK3 = sK10(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f46,f41])).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(resolution,[],[f23,f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK10(X0,X1,X2,X3),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(cnf_transformation,[],[f22])).
% 1.26/0.54  fof(f46,plain,(
% 1.26/0.54    ~m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | sK3 = sK10(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(trivial_inequality_removal,[],[f44])).
% 1.26/0.54  fof(f44,plain,(
% 1.26/0.54    sK4 != sK4 | sK3 = sK10(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.26/0.54    inference(superposition,[],[f24,f42])).
% 1.26/0.54  fof(f24,plain,(
% 1.26/0.54    ( ! [X6,X7,X5] : (k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  fof(f28,plain,(
% 1.26/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  fof(f27,plain,(
% 1.26/0.54    k1_xboole_0 != sK2),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  fof(f26,plain,(
% 1.26/0.54    k1_xboole_0 != sK1),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  fof(f25,plain,(
% 1.26/0.54    k1_xboole_0 != sK0),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (25953)------------------------------
% 1.26/0.54  % (25953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (25953)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (25953)Memory used [KB]: 1791
% 1.26/0.54  % (25953)Time elapsed: 0.120 s
% 1.26/0.54  % (25953)------------------------------
% 1.26/0.54  % (25953)------------------------------
% 1.26/0.54  % (25971)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.26/0.54  % (25951)Success in time 0.179 s
%------------------------------------------------------------------------------
