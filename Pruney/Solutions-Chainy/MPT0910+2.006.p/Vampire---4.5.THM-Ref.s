%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 230 expanded)
%              Number of leaves         :    9 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  275 (1979 expanded)
%              Number of equality atoms :  177 (1181 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f47,f43,f28,f97,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK1)
      | sK3 = X1
      | sK4 != k3_mcart_1(X0,X1,sK10(sK0,sK1,sK2,sK4))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f55,f24])).

fof(f24,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X6
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
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
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
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
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f55,plain,(
    m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) ),
    inference(subsumption_resolution,[],[f54,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f53,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f52,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f36,f23])).

fof(f23,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK10(X0,X1,X2,X3),X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f11,f21,f20,f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f97,plain,(
    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) ),
    inference(backward_demodulation,[],[f62,f95])).

fof(f95,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f94,f25])).

fof(f94,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f93,f26])).

fof(f93,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f92,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f80,f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2))
      | sK9(sK0,sK1,sK2,sK4) = k6_mcart_1(X0,X1,X2,sK4)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f79,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,sK4),X1)
      | sK9(sK0,sK1,sK2,sK4) = k6_mcart_1(X0,X1,X2,sK4)
      | ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f40,f62])).

fof(f40,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X1)
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X10,X8,X1,X9] :
      ( X4 = X9
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X10,X8,X3,X1,X9] :
      ( X4 = X9
      | k3_mcart_1(X8,X9,X10) != X3
      | k6_mcart_1(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK6(X3,X4) != X4
                    & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X6
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK6(X3,X4) != X4
        & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_mcart_1)).

fof(f62,plain,(
    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f61,f25])).

fof(f61,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f59,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f37,f23])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f14])).

% (26711)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f43,plain,(
    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) ),
    inference(resolution,[],[f38,f23])).

fof(f47,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f46,f25])).

fof(f46,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f45,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f44,f27])).

fof(f44,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f34,f23])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK8(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (26710)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.49  % (26718)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.49  % (26710)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f47,f43,f28,f97,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,sK1) | sK3 = X1 | sK4 != k3_mcart_1(X0,X1,sK10(sK0,sK1,sK2,sK4)) | ~m1_subset_1(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f55,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X6,X7,X5] : (~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X6 | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    k1_xboole_0 != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f36,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK10(X0,X1,X2,X3),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 & m1_subset_1(sK10(X0,X1,X2,X3),X2)) & m1_subset_1(sK9(X0,X1,X2,X3),X1)) & m1_subset_1(sK8(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f11,f21,f20,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8(X0,X1,X2,X3),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK9(X0,X1,X2,X3),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 & m1_subset_1(sK10(X0,X1,X2,X3),X2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))),
% 0.21/0.49    inference(backward_demodulation,[],[f62,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f25])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f26])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f27])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    k6_mcart_1(sK0,sK1,sK2,sK4) = sK9(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f80,f23])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2)) | sK9(sK0,sK1,sK2,sK4) = k6_mcart_1(X0,X1,X2,sK4) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(k6_mcart_1(X0,X1,X2,sK4),X1) | sK9(sK0,sK1,sK2,sK4) = k6_mcart_1(X0,X1,X2,sK4) | ~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(superposition,[],[f40,f62])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X10,X8,X1,X9] : (~m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)),X1) | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) = X9 | ~m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(equality_resolution,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X10,X8,X1,X9] : (X4 = X9 | k6_mcart_1(X0,X1,X2,k3_mcart_1(X8,X9,X10)) != X4 | ~m1_subset_1(X4,X1) | ~m1_subset_1(k3_mcart_1(X8,X9,X10),k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(equality_resolution,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X10,X8,X3,X1,X9] : (X4 = X9 | k3_mcart_1(X8,X9,X10) != X3 | k6_mcart_1(X0,X1,X2,X3) != X4 | ~m1_subset_1(X4,X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k6_mcart_1(X0,X1,X2,X3) = X4 | (sK6(X3,X4) != X4 & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3)) & (! [X8,X9,X10] : (X4 = X9 | k3_mcart_1(X8,X9,X10) != X3) | k6_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X4,X3] : (? [X5,X6,X7] : (X4 != X6 & k3_mcart_1(X5,X6,X7) = X3) => (sK6(X3,X4) != X4 & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k6_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X6 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X8,X9,X10] : (X4 = X9 | k3_mcart_1(X8,X9,X10) != X3) | k6_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(rectify,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k6_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X6 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X5,X6,X7] : (X4 = X6 | k3_mcart_1(X5,X6,X7) != X3) | k6_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((k6_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (X4 = X6 | k3_mcart_1(X5,X6,X7) != X3)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ! [X4] : (m1_subset_1(X4,X1) => (k6_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (k3_mcart_1(X5,X6,X7) = X3 => X4 = X6)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_mcart_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))),
% 0.21/0.49    inference(subsumption_resolution,[],[f61,f25])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f60,f26])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f27])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f37,f23])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % (26711)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)),
% 0.21/0.50    inference(resolution,[],[f38,f23])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f46,f25])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f45,f26])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f44,f27])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(resolution,[],[f34,f23])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK8(X0,X1,X2,X3),X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (26710)------------------------------
% 0.21/0.50  % (26710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26710)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (26710)Memory used [KB]: 1791
% 0.21/0.50  % (26710)Time elapsed: 0.075 s
% 0.21/0.50  % (26710)------------------------------
% 0.21/0.50  % (26710)------------------------------
% 0.21/0.50  % (26702)Success in time 0.15 s
%------------------------------------------------------------------------------
