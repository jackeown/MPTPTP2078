%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 257 expanded)
%              Number of leaves         :    8 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 (1310 expanded)
%              Number of equality atoms :  112 ( 955 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f19])).

fof(f19,plain,(
    sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f9,f8])).

fof(f8,plain,
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

fof(f9,plain,
    ( ? [X3] :
        ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,X3),k6_mcart_1(sK0,sK1,sK2,X3),k7_mcart_1(sK0,sK1,sK2,X3)) != X3
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f59,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f51,f57])).

fof(f57,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = sK6(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f40])).

fof(f40,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8))
      | sK6(sK0,sK1,sK2,sK3) = k7_mcart_1(X6,X7,X8,sK3)
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6 ) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    sK3 = k3_mcart_1(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3),sK6(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f6,f13,f12,f11])).

fof(f11,plain,(
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

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK6(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f18,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK6(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f45,f49])).

fof(f49,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = sK5(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f39])).

fof(f39,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5))
      | sK5(sK0,sK1,sK2,sK3) = k6_mcart_1(X3,X4,X5,sK3)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f28,f33])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3),sK6(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f33,f41])).

fof(f41,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = sK4(sK0,sK1,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | sK4(sK0,sK1,sK2,sK3) = k5_mcart_1(X0,X1,X2,sK3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f29,f33])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (25643)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.42  % (25643)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f59,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    (sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f9,f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (? [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3 & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : (k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,X3),k6_mcart_1(sK0,sK1,sK2,X3),k7_mcart_1(sK0,sK1,sK2,X3)) != X3 & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X3] : (k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,X3),k6_mcart_1(sK0,sK1,sK2,X3),k7_mcart_1(sK0,sK1,sK2,X3)) != X3 & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => (sK3 != k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (? [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) != X3 & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.42    inference(backward_demodulation,[],[f51,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    k7_mcart_1(sK0,sK1,sK2,sK3) = sK6(sK0,sK1,sK2,sK3)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X6,X8,X7] : (~m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8)) | sK6(sK0,sK1,sK2,sK3) = k7_mcart_1(X6,X7,X8,sK3) | k1_xboole_0 = X8 | k1_xboole_0 = X7 | k1_xboole_0 = X6) )),
% 0.21/0.42    inference(superposition,[],[f27,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    sK3 = k3_mcart_1(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3),sK6(sK0,sK1,sK2,sK3))),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3 & m1_subset_1(sK6(X0,X1,X2,X3),X2)) & m1_subset_1(sK5(X0,X1,X2,X3),X1)) & m1_subset_1(sK4(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f6,f13,f12,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4(X0,X1,X2,X3),X0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK5(X0,X1,X2,X3),X1)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3 & m1_subset_1(sK6(X0,X1,X2,X3),X2)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(equality_resolution,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = X6 | k3_mcart_1(X4,X5,X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (! [X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ~(? [X3] : (? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    k1_xboole_0 != sK2),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k1_xboole_0 != sK1),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k1_xboole_0 != sK0),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK6(sK0,sK1,sK2,sK3))),
% 0.21/0.42    inference(backward_demodulation,[],[f45,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    k6_mcart_1(sK0,sK1,sK2,sK3) = sK5(sK0,sK1,sK2,sK3)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5)) | sK5(sK0,sK1,sK2,sK3) = k6_mcart_1(X3,X4,X5,sK3) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3) )),
% 0.21/0.42    inference(superposition,[],[f28,f33])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(equality_resolution,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k3_mcart_1(X4,X5,X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3),sK6(sK0,sK1,sK2,sK3))),
% 0.21/0.42    inference(backward_demodulation,[],[f33,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    k5_mcart_1(sK0,sK1,sK2,sK3) = sK4(sK0,sK1,sK2,sK3)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2)) | sK4(sK0,sK1,sK2,sK3) = k5_mcart_1(X0,X1,X2,sK3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(superposition,[],[f29,f33])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(equality_resolution,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = X4 | k3_mcart_1(X4,X5,X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (25643)------------------------------
% 0.21/0.42  % (25643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (25635)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.43  % (25643)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (25643)Memory used [KB]: 6140
% 0.21/0.43  % (25643)Time elapsed: 0.009 s
% 0.21/0.43  % (25643)------------------------------
% 0.21/0.43  % (25643)------------------------------
% 0.21/0.43  % (25627)Success in time 0.077 s
%------------------------------------------------------------------------------
