%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0888+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 4.14s
% Output     : Refutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 278 expanded)
%              Number of leaves         :    8 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  194 (1373 expanded)
%              Number of equality atoms :  148 (1018 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6140,f2899])).

fof(f2899,plain,(
    sK24 != k3_mcart_1(k5_mcart_1(sK21,sK22,sK23,sK24),k6_mcart_1(sK21,sK22,sK23,sK24),k7_mcart_1(sK21,sK22,sK23,sK24)) ),
    inference(cnf_transformation,[],[f2270])).

fof(f2270,plain,
    ( sK24 != k3_mcart_1(k5_mcart_1(sK21,sK22,sK23,sK24),k6_mcart_1(sK21,sK22,sK23,sK24),k7_mcart_1(sK21,sK22,sK23,sK24))
    & m1_subset_1(sK24,k3_zfmisc_1(sK21,sK22,sK23))
    & k1_xboole_0 != sK23
    & k1_xboole_0 != sK22
    & k1_xboole_0 != sK21 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22,sK23,sK24])],[f1387,f2269,f2268])).

fof(f2268,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(sK21,sK22,sK23,X3),k6_mcart_1(sK21,sK22,sK23,X3),k7_mcart_1(sK21,sK22,sK23,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(sK21,sK22,sK23)) )
      & k1_xboole_0 != sK23
      & k1_xboole_0 != sK22
      & k1_xboole_0 != sK21 ) ),
    introduced(choice_axiom,[])).

fof(f2269,plain,
    ( ? [X3] :
        ( k3_mcart_1(k5_mcart_1(sK21,sK22,sK23,X3),k6_mcart_1(sK21,sK22,sK23,X3),k7_mcart_1(sK21,sK22,sK23,X3)) != X3
        & m1_subset_1(X3,k3_zfmisc_1(sK21,sK22,sK23)) )
   => ( sK24 != k3_mcart_1(k5_mcart_1(sK21,sK22,sK23,sK24),k6_mcart_1(sK21,sK22,sK23,sK24),k7_mcart_1(sK21,sK22,sK23,sK24))
      & m1_subset_1(sK24,k3_zfmisc_1(sK21,sK22,sK23)) ) ),
    introduced(choice_axiom,[])).

fof(f1387,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1343])).

fof(f1343,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1342])).

fof(f1342,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f6140,plain,(
    sK24 = k3_mcart_1(k5_mcart_1(sK21,sK22,sK23,sK24),k6_mcart_1(sK21,sK22,sK23,sK24),k7_mcart_1(sK21,sK22,sK23,sK24)) ),
    inference(backward_demodulation,[],[f5960,f6136])).

fof(f6136,plain,(
    k5_mcart_1(sK21,sK22,sK23,sK24) = sK25(sK21,sK22,sK23,sK24) ),
    inference(subsumption_resolution,[],[f6135,f2895])).

fof(f2895,plain,(
    k1_xboole_0 != sK21 ),
    inference(cnf_transformation,[],[f2270])).

fof(f6135,plain,
    ( k5_mcart_1(sK21,sK22,sK23,sK24) = sK25(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f6134,f2896])).

fof(f2896,plain,(
    k1_xboole_0 != sK22 ),
    inference(cnf_transformation,[],[f2270])).

fof(f6134,plain,
    ( k5_mcart_1(sK21,sK22,sK23,sK24) = sK25(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f6129,f2897])).

fof(f2897,plain,(
    k1_xboole_0 != sK23 ),
    inference(cnf_transformation,[],[f2270])).

fof(f6129,plain,
    ( k5_mcart_1(sK21,sK22,sK23,sK24) = sK25(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK23
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(resolution,[],[f4620,f2898])).

fof(f2898,plain,(
    m1_subset_1(sK24,k3_zfmisc_1(sK21,sK22,sK23)) ),
    inference(cnf_transformation,[],[f2270])).

fof(f4620,plain,(
    ! [X83,X81,X82] :
      ( ~ m1_subset_1(sK24,k3_zfmisc_1(X81,X82,X83))
      | sK25(sK21,sK22,sK23,sK24) = k5_mcart_1(X81,X82,X83,sK24)
      | k1_xboole_0 = X83
      | k1_xboole_0 = X82
      | k1_xboole_0 = X81 ) ),
    inference(superposition,[],[f4394,f4564])).

fof(f4564,plain,(
    sK24 = k3_mcart_1(sK25(sK21,sK22,sK23,sK24),sK26(sK21,sK22,sK23,sK24),sK27(sK21,sK22,sK23,sK24)) ),
    inference(subsumption_resolution,[],[f4563,f2895])).

fof(f4563,plain,
    ( sK24 = k3_mcart_1(sK25(sK21,sK22,sK23,sK24),sK26(sK21,sK22,sK23,sK24),sK27(sK21,sK22,sK23,sK24))
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f4562,f2896])).

fof(f4562,plain,
    ( sK24 = k3_mcart_1(sK25(sK21,sK22,sK23,sK24),sK26(sK21,sK22,sK23,sK24),sK27(sK21,sK22,sK23,sK24))
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f4548,f2897])).

fof(f4548,plain,
    ( sK24 = k3_mcart_1(sK25(sK21,sK22,sK23,sK24),sK26(sK21,sK22,sK23,sK24),sK27(sK21,sK22,sK23,sK24))
    | k1_xboole_0 = sK23
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(resolution,[],[f2898,f2918])).

fof(f2918,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK25(X0,X1,X2,X3),sK26(X0,X1,X2,X3),sK27(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2274])).

fof(f2274,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK25(X0,X1,X2,X3),sK26(X0,X1,X2,X3),sK27(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK27(X0,X1,X2,X3),X2)
            & m1_subset_1(sK26(X0,X1,X2,X3),X1)
            & m1_subset_1(sK25(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27])],[f1390,f2273,f2272,f2271])).

fof(f2271,plain,(
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
                ( k3_mcart_1(sK25(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK25(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2272,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK25(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK25(X0,X1,X2,X3),sK26(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK26(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f2273,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK25(X0,X1,X2,X3),sK26(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK25(X0,X1,X2,X3),sK26(X0,X1,X2,X3),sK27(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK27(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f1390,plain,(
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
    inference(ennf_transformation,[],[f1289])).

fof(f1289,axiom,(
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

fof(f4394,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2912])).

fof(f2912,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1389])).

fof(f1389,plain,(
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
    inference(ennf_transformation,[],[f1341])).

fof(f1341,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

fof(f5960,plain,(
    sK24 = k3_mcart_1(sK25(sK21,sK22,sK23,sK24),k6_mcart_1(sK21,sK22,sK23,sK24),k7_mcart_1(sK21,sK22,sK23,sK24)) ),
    inference(backward_demodulation,[],[f5793,f5956])).

fof(f5956,plain,(
    k6_mcart_1(sK21,sK22,sK23,sK24) = sK26(sK21,sK22,sK23,sK24) ),
    inference(subsumption_resolution,[],[f5955,f2895])).

fof(f5955,plain,
    ( k6_mcart_1(sK21,sK22,sK23,sK24) = sK26(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f5954,f2896])).

fof(f5954,plain,
    ( k6_mcart_1(sK21,sK22,sK23,sK24) = sK26(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f5949,f2897])).

fof(f5949,plain,
    ( k6_mcart_1(sK21,sK22,sK23,sK24) = sK26(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK23
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(resolution,[],[f4619,f2898])).

fof(f4619,plain,(
    ! [X80,X78,X79] :
      ( ~ m1_subset_1(sK24,k3_zfmisc_1(X78,X79,X80))
      | sK26(sK21,sK22,sK23,sK24) = k6_mcart_1(X78,X79,X80,sK24)
      | k1_xboole_0 = X80
      | k1_xboole_0 = X79
      | k1_xboole_0 = X78 ) ),
    inference(superposition,[],[f4393,f4564])).

fof(f4393,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2913])).

fof(f2913,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1389])).

fof(f5793,plain,(
    sK24 = k3_mcart_1(sK25(sK21,sK22,sK23,sK24),sK26(sK21,sK22,sK23,sK24),k7_mcart_1(sK21,sK22,sK23,sK24)) ),
    inference(backward_demodulation,[],[f4564,f5792])).

fof(f5792,plain,(
    k7_mcart_1(sK21,sK22,sK23,sK24) = sK27(sK21,sK22,sK23,sK24) ),
    inference(subsumption_resolution,[],[f5791,f2895])).

fof(f5791,plain,
    ( k7_mcart_1(sK21,sK22,sK23,sK24) = sK27(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f5790,f2896])).

fof(f5790,plain,
    ( k7_mcart_1(sK21,sK22,sK23,sK24) = sK27(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(subsumption_resolution,[],[f5785,f2897])).

fof(f5785,plain,
    ( k7_mcart_1(sK21,sK22,sK23,sK24) = sK27(sK21,sK22,sK23,sK24)
    | k1_xboole_0 = sK23
    | k1_xboole_0 = sK22
    | k1_xboole_0 = sK21 ),
    inference(resolution,[],[f4618,f2898])).

fof(f4618,plain,(
    ! [X76,X77,X75] :
      ( ~ m1_subset_1(sK24,k3_zfmisc_1(X75,X76,X77))
      | sK27(sK21,sK22,sK23,sK24) = k7_mcart_1(X75,X76,X77,sK24)
      | k1_xboole_0 = X77
      | k1_xboole_0 = X76
      | k1_xboole_0 = X75 ) ),
    inference(superposition,[],[f4392,f4564])).

fof(f4392,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2914])).

fof(f2914,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1389])).
%------------------------------------------------------------------------------
