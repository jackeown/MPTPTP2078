%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0900+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 3.54s
% Output     : Refutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 432 expanded)
%              Number of leaves         :    9 ( 167 expanded)
%              Depth                    :   20
%              Number of atoms          :  286 (2502 expanded)
%              Number of equality atoms :  226 (1924 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6034,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6033,f2879])).

fof(f2879,plain,(
    sK22 != k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK22),k9_mcart_1(sK18,sK19,sK20,sK21,sK22),k10_mcart_1(sK18,sK19,sK20,sK21,sK22),k11_mcart_1(sK18,sK19,sK20,sK21,sK22)) ),
    inference(cnf_transformation,[],[f2269])).

fof(f2269,plain,
    ( sK22 != k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK22),k9_mcart_1(sK18,sK19,sK20,sK21,sK22),k10_mcart_1(sK18,sK19,sK20,sK21,sK22),k11_mcart_1(sK18,sK19,sK20,sK21,sK22))
    & m1_subset_1(sK22,k4_zfmisc_1(sK18,sK19,sK20,sK21))
    & k1_xboole_0 != sK21
    & k1_xboole_0 != sK20
    & k1_xboole_0 != sK19
    & k1_xboole_0 != sK18 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22])],[f1405,f2268,f2267])).

fof(f2267,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,X4),k9_mcart_1(sK18,sK19,sK20,sK21,X4),k10_mcart_1(sK18,sK19,sK20,sK21,X4),k11_mcart_1(sK18,sK19,sK20,sK21,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(sK18,sK19,sK20,sK21)) )
      & k1_xboole_0 != sK21
      & k1_xboole_0 != sK20
      & k1_xboole_0 != sK19
      & k1_xboole_0 != sK18 ) ),
    introduced(choice_axiom,[])).

fof(f2268,plain,
    ( ? [X4] :
        ( k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,X4),k9_mcart_1(sK18,sK19,sK20,sK21,X4),k10_mcart_1(sK18,sK19,sK20,sK21,X4),k11_mcart_1(sK18,sK19,sK20,sK21,X4)) != X4
        & m1_subset_1(X4,k4_zfmisc_1(sK18,sK19,sK20,sK21)) )
   => ( sK22 != k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK22),k9_mcart_1(sK18,sK19,sK20,sK21,sK22),k10_mcart_1(sK18,sK19,sK20,sK21,sK22),k11_mcart_1(sK18,sK19,sK20,sK21,sK22))
      & m1_subset_1(sK22,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ) ),
    introduced(choice_axiom,[])).

fof(f1405,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1368])).

fof(f1368,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1367])).

fof(f1367,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f6033,plain,(
    sK22 = k4_mcart_1(k8_mcart_1(sK18,sK19,sK20,sK21,sK22),k9_mcart_1(sK18,sK19,sK20,sK21,sK22),k10_mcart_1(sK18,sK19,sK20,sK21,sK22),k11_mcart_1(sK18,sK19,sK20,sK21,sK22)) ),
    inference(backward_demodulation,[],[f5902,f6030])).

fof(f6030,plain,(
    k8_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK23(sK18,sK19,sK20,sK21,sK22) ),
    inference(subsumption_resolution,[],[f6029,f2874])).

fof(f2874,plain,(
    k1_xboole_0 != sK18 ),
    inference(cnf_transformation,[],[f2269])).

fof(f6029,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK23(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f6028,f2875])).

fof(f2875,plain,(
    k1_xboole_0 != sK19 ),
    inference(cnf_transformation,[],[f2269])).

fof(f6028,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK23(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f6027,f2876])).

fof(f2876,plain,(
    k1_xboole_0 != sK20 ),
    inference(cnf_transformation,[],[f2269])).

fof(f6027,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK23(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f6022,f2877])).

fof(f2877,plain,(
    k1_xboole_0 != sK21 ),
    inference(cnf_transformation,[],[f2269])).

fof(f6022,plain,
    ( k8_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK23(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f4895,f2878])).

fof(f2878,plain,(
    m1_subset_1(sK22,k4_zfmisc_1(sK18,sK19,sK20,sK21)) ),
    inference(cnf_transformation,[],[f2269])).

fof(f4895,plain,(
    ! [X47,X48,X46,X49] :
      ( ~ m1_subset_1(sK22,k4_zfmisc_1(X46,X47,X48,X49))
      | sK23(sK18,sK19,sK20,sK21,sK22) = k8_mcart_1(X46,X47,X48,X49,sK22)
      | k1_xboole_0 = X49
      | k1_xboole_0 = X48
      | k1_xboole_0 = X47
      | k1_xboole_0 = X46 ) ),
    inference(superposition,[],[f4353,f4537])).

fof(f4537,plain,(
    sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),sK24(sK18,sK19,sK20,sK21,sK22),sK25(sK18,sK19,sK20,sK21,sK22),sK26(sK18,sK19,sK20,sK21,sK22)) ),
    inference(subsumption_resolution,[],[f4536,f2874])).

fof(f4536,plain,
    ( sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),sK24(sK18,sK19,sK20,sK21,sK22),sK25(sK18,sK19,sK20,sK21,sK22),sK26(sK18,sK19,sK20,sK21,sK22))
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4535,f2875])).

fof(f4535,plain,
    ( sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),sK24(sK18,sK19,sK20,sK21,sK22),sK25(sK18,sK19,sK20,sK21,sK22),sK26(sK18,sK19,sK20,sK21,sK22))
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4534,f2876])).

fof(f4534,plain,
    ( sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),sK24(sK18,sK19,sK20,sK21,sK22),sK25(sK18,sK19,sK20,sK21,sK22),sK26(sK18,sK19,sK20,sK21,sK22))
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f4514,f2877])).

fof(f4514,plain,
    ( sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),sK24(sK18,sK19,sK20,sK21,sK22),sK25(sK18,sK19,sK20,sK21,sK22),sK26(sK18,sK19,sK20,sK21,sK22))
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f2878,f2892])).

fof(f2892,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK23(X0,X1,X2,X3,X4),sK24(X0,X1,X2,X3,X4),sK25(X0,X1,X2,X3,X4),sK26(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2274])).

fof(f2274,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),sK24(X0,X1,X2,X3,X4),sK25(X0,X1,X2,X3,X4),sK26(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK26(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK25(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK24(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK23(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24,sK25,sK26])],[f1408,f2273,f2272,f2271,f2270])).

fof(f2270,plain,(
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
                    ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK23(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2271,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),sK24(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK24(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f2272,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),sK24(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),sK24(X0,X1,X2,X3,X4),sK25(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK25(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f2273,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),sK24(X0,X1,X2,X3,X4),sK25(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK23(X0,X1,X2,X3,X4),sK24(X0,X1,X2,X3,X4),sK25(X0,X1,X2,X3,X4),sK26(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK26(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f1408,plain,(
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
    inference(ennf_transformation,[],[f1300])).

fof(f1300,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f4353,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2884])).

fof(f2884,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f1407,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              | k4_mcart_1(X5,X6,X7,X8) != X4 )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1365])).

fof(f1365,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f5902,plain,(
    sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),k9_mcart_1(sK18,sK19,sK20,sK21,sK22),k10_mcart_1(sK18,sK19,sK20,sK21,sK22),k11_mcart_1(sK18,sK19,sK20,sK21,sK22)) ),
    inference(backward_demodulation,[],[f5805,f5899])).

fof(f5899,plain,(
    k9_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK24(sK18,sK19,sK20,sK21,sK22) ),
    inference(subsumption_resolution,[],[f5898,f2874])).

fof(f5898,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK24(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5897,f2875])).

fof(f5897,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK24(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5896,f2876])).

fof(f5896,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK24(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5891,f2877])).

fof(f5891,plain,
    ( k9_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK24(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f4894,f2878])).

fof(f4894,plain,(
    ! [X45,X43,X44,X42] :
      ( ~ m1_subset_1(sK22,k4_zfmisc_1(X42,X43,X44,X45))
      | sK24(sK18,sK19,sK20,sK21,sK22) = k9_mcart_1(X42,X43,X44,X45,sK22)
      | k1_xboole_0 = X45
      | k1_xboole_0 = X44
      | k1_xboole_0 = X43
      | k1_xboole_0 = X42 ) ),
    inference(superposition,[],[f4352,f4537])).

fof(f4352,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X6
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2885])).

fof(f2885,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f5805,plain,(
    sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),sK24(sK18,sK19,sK20,sK21,sK22),k10_mcart_1(sK18,sK19,sK20,sK21,sK22),k11_mcart_1(sK18,sK19,sK20,sK21,sK22)) ),
    inference(backward_demodulation,[],[f5709,f5803])).

fof(f5803,plain,(
    k10_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK25(sK18,sK19,sK20,sK21,sK22) ),
    inference(subsumption_resolution,[],[f5802,f2874])).

fof(f5802,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK25(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5801,f2875])).

fof(f5801,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK25(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5800,f2876])).

fof(f5800,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK25(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5795,f2877])).

fof(f5795,plain,
    ( k10_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK25(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f4893,f2878])).

fof(f4893,plain,(
    ! [X39,X41,X38,X40] :
      ( ~ m1_subset_1(sK22,k4_zfmisc_1(X38,X39,X40,X41))
      | sK25(sK18,sK19,sK20,sK21,sK22) = k10_mcart_1(X38,X39,X40,X41,sK22)
      | k1_xboole_0 = X41
      | k1_xboole_0 = X40
      | k1_xboole_0 = X39
      | k1_xboole_0 = X38 ) ),
    inference(superposition,[],[f4351,f4537])).

fof(f4351,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2886])).

fof(f2886,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f5709,plain,(
    sK22 = k4_mcart_1(sK23(sK18,sK19,sK20,sK21,sK22),sK24(sK18,sK19,sK20,sK21,sK22),sK25(sK18,sK19,sK20,sK21,sK22),k11_mcart_1(sK18,sK19,sK20,sK21,sK22)) ),
    inference(backward_demodulation,[],[f4537,f5708])).

fof(f5708,plain,(
    k11_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK26(sK18,sK19,sK20,sK21,sK22) ),
    inference(subsumption_resolution,[],[f5707,f2874])).

fof(f5707,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK26(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5706,f2875])).

fof(f5706,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK26(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5705,f2876])).

fof(f5705,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK26(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(subsumption_resolution,[],[f5700,f2877])).

fof(f5700,plain,
    ( k11_mcart_1(sK18,sK19,sK20,sK21,sK22) = sK26(sK18,sK19,sK20,sK21,sK22)
    | k1_xboole_0 = sK21
    | k1_xboole_0 = sK20
    | k1_xboole_0 = sK19
    | k1_xboole_0 = sK18 ),
    inference(resolution,[],[f4892,f2878])).

fof(f4892,plain,(
    ! [X37,X35,X36,X34] :
      ( ~ m1_subset_1(sK22,k4_zfmisc_1(X34,X35,X36,X37))
      | sK26(sK18,sK19,sK20,sK21,sK22) = k11_mcart_1(X34,X35,X36,X37,sK22)
      | k1_xboole_0 = X37
      | k1_xboole_0 = X36
      | k1_xboole_0 = X35
      | k1_xboole_0 = X34 ) ),
    inference(superposition,[],[f4350,f4537])).

fof(f4350,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2887])).

fof(f2887,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).
%------------------------------------------------------------------------------
