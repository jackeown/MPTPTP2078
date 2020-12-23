%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  116 (1570 expanded)
%              Number of leaves         :   10 ( 414 expanded)
%              Depth                    :   25
%              Number of atoms          :  480 (16373 expanded)
%              Number of equality atoms :  343 (9901 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(global_subsumption,[],[f144,f152,f161,f171])).

fof(f171,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) ),
    inference(subsumption_resolution,[],[f170,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X9
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

fof(f170,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f169,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f169,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f168,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f168,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f167,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f167,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f163,f20])).

fof(f20,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f163,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f32,f135])).

fof(f135,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( sK5 != sK5
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f96,f118])).

fof(f118,plain,(
    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f117,f22])).

fof(f117,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f116,f23])).

fof(f116,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f115,f24])).

fof(f115,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f110,f25])).

fof(f110,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f36,f20])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f11,f18,f17,f16,f15])).

fof(f15,plain,(
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
                    ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != sK5
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(superposition,[],[f37,f94])).

fof(f94,plain,(
    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5)) ),
    inference(forward_demodulation,[],[f93,f72])).

fof(f72,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f71,f22])).

fof(f71,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f70,f23])).

% (17665)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f70,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f69,f24])).

fof(f69,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f64,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f28,f20])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f93,plain,(
    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5)) ),
    inference(forward_demodulation,[],[f92,f81])).

fof(f81,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f79,f23])).

fof(f79,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f78,f24])).

fof(f78,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f73,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f29,f20])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f92,plain,(
    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5)) ),
    inference(forward_demodulation,[],[f91,f63])).

fof(f63,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f62,f22])).

fof(f62,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f61,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f60,f24])).

fof(f60,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f55,f25])).

fof(f55,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f30,f20])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,(
    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(sK5)) ),
    inference(forward_demodulation,[],[f90,f53])).

fof(f53,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f52,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f51,f23])).

fof(f51,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f50,f24])).

fof(f50,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f45,f25])).

fof(f45,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f31,f20])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f89,f22])).

fof(f89,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f88,f23])).

fof(f88,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f87,f24])).

fof(f87,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f82,f25])).

fof(f82,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f161,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) ),
    inference(subsumption_resolution,[],[f160,f22])).

fof(f160,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f159,f23])).

fof(f159,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f158,f24])).

fof(f158,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f157,f25])).

fof(f157,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f154,f20])).

fof(f154,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f33,f134])).

fof(f134,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,
    ( sK5 != sK5
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f98,f118])).

fof(f98,plain,(
    ! [X10,X8,X11,X9] :
      ( sK5 != k4_mcart_1(X8,X9,X10,X11)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X9 ) ),
    inference(superposition,[],[f38,f94])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X1 = X5 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f152,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) ),
    inference(subsumption_resolution,[],[f151,f22])).

fof(f151,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f150,f23])).

fof(f150,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f149,f24])).

fof(f149,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f148,f25])).

fof(f148,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f146,f20])).

fof(f146,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f34,f133])).

fof(f133,plain,(
    k2_mcart_1(k1_mcart_1(sK5)) = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( sK5 != sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f100,f118])).

fof(f100,plain,(
    ! [X19,X17,X18,X16] :
      ( sK5 != k4_mcart_1(X16,X17,X18,X19)
      | k2_mcart_1(k1_mcart_1(sK5)) = X18 ) ),
    inference(superposition,[],[f39,f94])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X2 = X6 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f144,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) ),
    inference(resolution,[],[f143,f105])).

fof(f105,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) ),
    inference(subsumption_resolution,[],[f104,f54])).

fof(f54,plain,(
    sK4 != k2_mcart_1(sK5) ),
    inference(superposition,[],[f26,f53])).

fof(f26,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f104,plain,
    ( sK4 = k2_mcart_1(sK5)
    | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,
    ( sK5 != sK5
    | sK4 = k2_mcart_1(sK5)
    | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) ),
    inference(superposition,[],[f21,f94])).

fof(f21,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X9
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f143,plain,(
    m1_subset_1(k2_mcart_1(sK5),sK3) ),
    inference(subsumption_resolution,[],[f142,f22])).

fof(f142,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f141,f23])).

fof(f141,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f140,f24])).

fof(f140,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f139,f25])).

fof(f139,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f138,f20])).

fof(f138,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f35,f132])).

fof(f132,plain,(
    k2_mcart_1(sK5) = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( sK5 != sK5
    | k2_mcart_1(sK5) = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f102,f118])).

fof(f102,plain,(
    ! [X26,X24,X27,X25] :
      ( sK5 != k4_mcart_1(X24,X25,X26,X27)
      | k2_mcart_1(sK5) = X27 ) ),
    inference(superposition,[],[f40,f94])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X3 = X7 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:48:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.46  % (17685)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.48  % (17685)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f172,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(global_subsumption,[],[f144,f152,f161,f171])).
% 0.23/0.48  fof(f171,plain,(
% 0.23/0.48    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)),
% 0.23/0.48    inference(subsumption_resolution,[],[f170,f22])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    k1_xboole_0 != sK0),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f13])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f8,plain,(
% 0.23/0.48    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.23/0.48    inference(flattening,[],[f7])).
% 0.23/0.48  fof(f7,plain,(
% 0.23/0.48    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.23/0.48    inference(ennf_transformation,[],[f6])).
% 0.23/0.48  fof(f6,negated_conjecture,(
% 0.23/0.48    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.23/0.48    inference(negated_conjecture,[],[f5])).
% 0.23/0.48  fof(f5,conjecture,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).
% 0.23/0.48  fof(f170,plain,(
% 0.23/0.48    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f169,f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    k1_xboole_0 != sK1),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f169,plain,(
% 0.23/0.48    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f168,f24])).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    k1_xboole_0 != sK2),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f168,plain,(
% 0.23/0.48    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f167,f25])).
% 0.23/0.48  fof(f25,plain,(
% 0.23/0.48    k1_xboole_0 != sK3),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f167,plain,(
% 0.23/0.48    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f163,f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f163,plain,(
% 0.23/0.48    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(superposition,[],[f32,f135])).
% 0.23/0.48  fof(f135,plain,(
% 0.23/0.48    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.48    inference(trivial_inequality_removal,[],[f128])).
% 0.23/0.48  fof(f128,plain,(
% 0.23/0.48    sK5 != sK5 | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.48    inference(superposition,[],[f96,f118])).
% 0.23/0.48  fof(f118,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.23/0.48    inference(subsumption_resolution,[],[f117,f22])).
% 0.23/0.48  fof(f117,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f116,f23])).
% 0.23/0.48  fof(f116,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f115,f24])).
% 0.23/0.48  fof(f115,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f110,f25])).
% 0.23/0.48  fof(f110,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(resolution,[],[f36,f20])).
% 0.23/0.48  fof(f36,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f19])).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f11,f18,f17,f16,f15])).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    ! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f11,plain,(
% 0.23/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.23/0.48    inference(ennf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.23/0.48  fof(f96,plain,(
% 0.23/0.48    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != sK5 | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.23/0.48    inference(superposition,[],[f37,f94])).
% 0.23/0.48  fof(f94,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))),
% 0.23/0.48    inference(forward_demodulation,[],[f93,f72])).
% 0.23/0.48  fof(f72,plain,(
% 0.23/0.48    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.23/0.48    inference(subsumption_resolution,[],[f71,f22])).
% 0.23/0.48  fof(f71,plain,(
% 0.23/0.48    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f70,f23])).
% 0.23/0.48  % (17665)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.48  fof(f70,plain,(
% 0.23/0.48    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f69,f24])).
% 0.23/0.48  fof(f69,plain,(
% 0.23/0.48    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f64,f25])).
% 0.23/0.48  fof(f64,plain,(
% 0.23/0.48    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(resolution,[],[f28,f20])).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,plain,(
% 0.23/0.48    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.23/0.48    inference(ennf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.23/0.48  fof(f93,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))),
% 0.23/0.48    inference(forward_demodulation,[],[f92,f81])).
% 0.23/0.48  fof(f81,plain,(
% 0.23/0.48    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.23/0.48    inference(subsumption_resolution,[],[f80,f22])).
% 0.23/0.48  fof(f80,plain,(
% 0.23/0.48    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f79,f23])).
% 0.23/0.48  fof(f79,plain,(
% 0.23/0.48    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f78,f24])).
% 0.23/0.48  fof(f78,plain,(
% 0.23/0.48    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f73,f25])).
% 0.23/0.48  fof(f73,plain,(
% 0.23/0.48    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(resolution,[],[f29,f20])).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f92,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))),
% 0.23/0.48    inference(forward_demodulation,[],[f91,f63])).
% 0.23/0.48  fof(f63,plain,(
% 0.23/0.48    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.23/0.48    inference(subsumption_resolution,[],[f62,f22])).
% 0.23/0.48  fof(f62,plain,(
% 0.23/0.48    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f61,f23])).
% 0.23/0.48  fof(f61,plain,(
% 0.23/0.48    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f60,f24])).
% 0.23/0.48  fof(f60,plain,(
% 0.23/0.48    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f55,f25])).
% 0.23/0.48  fof(f55,plain,(
% 0.23/0.48    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(resolution,[],[f30,f20])).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f91,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k2_mcart_1(sK5))),
% 0.23/0.48    inference(forward_demodulation,[],[f90,f53])).
% 0.23/0.48  fof(f53,plain,(
% 0.23/0.48    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.23/0.48    inference(subsumption_resolution,[],[f52,f22])).
% 0.23/0.48  fof(f52,plain,(
% 0.23/0.48    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f51,f23])).
% 0.23/0.48  fof(f51,plain,(
% 0.23/0.48    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f50,f24])).
% 0.23/0.48  fof(f50,plain,(
% 0.23/0.48    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f45,f25])).
% 0.23/0.48  fof(f45,plain,(
% 0.23/0.48    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(resolution,[],[f31,f20])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f90,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.23/0.48    inference(subsumption_resolution,[],[f89,f22])).
% 0.23/0.48  fof(f89,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f88,f23])).
% 0.23/0.48  fof(f88,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f87,f24])).
% 0.23/0.48  fof(f87,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f82,f25])).
% 0.23/0.48  fof(f82,plain,(
% 0.23/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(resolution,[],[f27,f20])).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,plain,(
% 0.23/0.48    ! [X0,X1,X2,X3] : (! [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.23/0.48    inference(ennf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.23/0.48  fof(f37,plain,(
% 0.23/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X0 = X4) )),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7))),
% 0.23/0.48    inference(ennf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.23/0.48  fof(f32,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f19])).
% 0.23/0.48  fof(f161,plain,(
% 0.23/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)),
% 0.23/0.48    inference(subsumption_resolution,[],[f160,f22])).
% 0.23/0.48  fof(f160,plain,(
% 0.23/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f159,f23])).
% 0.23/0.48  fof(f159,plain,(
% 0.23/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f158,f24])).
% 0.23/0.48  fof(f158,plain,(
% 0.23/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f157,f25])).
% 0.23/0.48  fof(f157,plain,(
% 0.23/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(subsumption_resolution,[],[f154,f20])).
% 0.23/0.48  fof(f154,plain,(
% 0.23/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.48    inference(superposition,[],[f33,f134])).
% 0.23/0.48  fof(f134,plain,(
% 0.23/0.48    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.48    inference(trivial_inequality_removal,[],[f129])).
% 0.23/0.48  fof(f129,plain,(
% 0.23/0.48    sK5 != sK5 | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.48    inference(superposition,[],[f98,f118])).
% 0.23/0.48  fof(f98,plain,(
% 0.23/0.48    ( ! [X10,X8,X11,X9] : (sK5 != k4_mcart_1(X8,X9,X10,X11) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X9) )),
% 0.23/0.48    inference(superposition,[],[f38,f94])).
% 0.23/0.48  fof(f38,plain,(
% 0.23/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X1 = X5) )),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f152,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)),
% 0.23/0.49    inference(subsumption_resolution,[],[f151,f22])).
% 0.23/0.49  fof(f151,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f150,f23])).
% 0.23/0.49  fof(f150,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f149,f24])).
% 0.23/0.49  fof(f149,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f148,f25])).
% 0.23/0.49  fof(f148,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f146,f20])).
% 0.23/0.49  fof(f146,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(superposition,[],[f34,f133])).
% 0.23/0.49  fof(f133,plain,(
% 0.23/0.49    k2_mcart_1(k1_mcart_1(sK5)) = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.49    inference(trivial_inequality_removal,[],[f130])).
% 0.23/0.49  fof(f130,plain,(
% 0.23/0.49    sK5 != sK5 | k2_mcart_1(k1_mcart_1(sK5)) = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.49    inference(superposition,[],[f100,f118])).
% 0.23/0.49  fof(f100,plain,(
% 0.23/0.49    ( ! [X19,X17,X18,X16] : (sK5 != k4_mcart_1(X16,X17,X18,X19) | k2_mcart_1(k1_mcart_1(sK5)) = X18) )),
% 0.23/0.49    inference(superposition,[],[f39,f94])).
% 0.23/0.49  fof(f39,plain,(
% 0.23/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X2 = X6) )),
% 0.23/0.49    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f144,plain,(
% 0.23/0.49    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)),
% 0.23/0.49    inference(resolution,[],[f143,f105])).
% 0.23/0.49  fof(f105,plain,(
% 0.23/0.49    ~m1_subset_1(k2_mcart_1(sK5),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)),
% 0.23/0.49    inference(subsumption_resolution,[],[f104,f54])).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    sK4 != k2_mcart_1(sK5)),
% 0.23/0.49    inference(superposition,[],[f26,f53])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.49    inference(cnf_transformation,[],[f14])).
% 0.23/0.49  fof(f104,plain,(
% 0.23/0.49    sK4 = k2_mcart_1(sK5) | ~m1_subset_1(k2_mcart_1(sK5),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)),
% 0.23/0.49    inference(trivial_inequality_removal,[],[f95])).
% 0.23/0.49  fof(f95,plain,(
% 0.23/0.49    sK5 != sK5 | sK4 = k2_mcart_1(sK5) | ~m1_subset_1(k2_mcart_1(sK5),sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)),
% 0.23/0.49    inference(superposition,[],[f21,f94])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X9 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f14])).
% 0.23/0.49  fof(f143,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(sK5),sK3)),
% 0.23/0.49    inference(subsumption_resolution,[],[f142,f22])).
% 0.23/0.49  fof(f142,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(sK5),sK3) | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f141,f23])).
% 0.23/0.49  fof(f141,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(sK5),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f140,f24])).
% 0.23/0.49  fof(f140,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(sK5),sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f139,f25])).
% 0.23/0.49  fof(f139,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(sK5),sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(subsumption_resolution,[],[f138,f20])).
% 0.23/0.49  fof(f138,plain,(
% 0.23/0.49    m1_subset_1(k2_mcart_1(sK5),sK3) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.49    inference(superposition,[],[f35,f132])).
% 0.23/0.49  fof(f132,plain,(
% 0.23/0.49    k2_mcart_1(sK5) = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.49    inference(trivial_inequality_removal,[],[f131])).
% 0.23/0.49  fof(f131,plain,(
% 0.23/0.49    sK5 != sK5 | k2_mcart_1(sK5) = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.23/0.49    inference(superposition,[],[f102,f118])).
% 0.23/0.49  fof(f102,plain,(
% 0.23/0.49    ( ! [X26,X24,X27,X25] : (sK5 != k4_mcart_1(X24,X25,X26,X27) | k2_mcart_1(sK5) = X27) )),
% 0.23/0.49    inference(superposition,[],[f40,f94])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X3 = X7) )),
% 0.23/0.49    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (17685)------------------------------
% 0.23/0.49  % (17685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (17685)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (17685)Memory used [KB]: 6652
% 0.23/0.49  % (17685)Time elapsed: 0.058 s
% 0.23/0.49  % (17685)------------------------------
% 0.23/0.49  % (17685)------------------------------
% 0.23/0.49  % (17658)Success in time 0.118 s
%------------------------------------------------------------------------------
