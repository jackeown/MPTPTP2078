%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   95 (1131 expanded)
%              Number of leaves         :    7 ( 229 expanded)
%              Depth                    :   28
%              Number of atoms          :  447 (8433 expanded)
%              Number of equality atoms :  334 (5306 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(subsumption_resolution,[],[f190,f162])).

fof(f162,plain,(
    ! [X0] : k2_mcart_1(k1_mcart_1(sK5)) = X0 ),
    inference(subsumption_resolution,[],[f161,f22])).

fof(f22,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f161,plain,(
    ! [X0] :
      ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f160,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f160,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f159,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f159,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f158,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f158,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f157,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f157,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(resolution,[],[f151,f41])).

fof(f41,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f17,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f17,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f151,plain,(
    ! [X45,X43,X46,X44,X42] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X43,X44,X45),X46))
      | k1_xboole_0 = X43
      | k1_xboole_0 = X44
      | k1_xboole_0 = X45
      | k1_xboole_0 = X46
      | sK4 = k11_mcart_1(X43,X44,X45,X46,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X42 ) ),
    inference(superposition,[],[f57,f141])).

fof(f141,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK4)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK4)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(superposition,[],[f117,f137])).

fof(f137,plain,(
    ! [X26] :
      ( sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X26 ) ),
    inference(subsumption_resolution,[],[f136,f112])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(forward_demodulation,[],[f90,f78])).

fof(f78,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f77,f18])).

fof(f77,plain,
    ( k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f76,f21])).

fof(f76,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f75,f20])).

fof(f75,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f62,f19])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(resolution,[],[f41,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f21])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f88,f20])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f87,f19])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f65,f18])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f39,f25])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f136,plain,(
    ! [X26] :
      ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X26 ) ),
    inference(subsumption_resolution,[],[f135,f116])).

fof(f116,plain,(
    ! [X5] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3)
      | k2_mcart_1(k1_mcart_1(sK5)) = X5 ) ),
    inference(forward_demodulation,[],[f110,f78])).

fof(f110,plain,(
    ! [X5] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f109,f21])).

fof(f109,plain,(
    ! [X5] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f108,f20])).

fof(f108,plain,(
    ! [X5] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f107,f19])).

fof(f107,plain,(
    ! [X5] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f70,plain,(
    ! [X5] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f34,f25])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f135,plain,(
    ! [X26] :
      ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X26 ) ),
    inference(subsumption_resolution,[],[f134,f114])).

fof(f114,plain,(
    ! [X2] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2)
      | k2_mcart_1(k1_mcart_1(sK5)) = X2 ) ),
    inference(forward_demodulation,[],[f98,f78])).

fof(f98,plain,(
    ! [X2] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f97,f21])).

fof(f97,plain,(
    ! [X2] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f96,f20])).

fof(f96,plain,(
    ! [X2] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f95,f19])).

fof(f95,plain,(
    ! [X2] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f67,f18])).

fof(f67,plain,(
    ! [X2] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f37,f25])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f134,plain,(
    ! [X26] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X26,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X26 ) ),
    inference(subsumption_resolution,[],[f133,f113])).

fof(f113,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1)
      | k2_mcart_1(k1_mcart_1(sK5)) = X1 ) ),
    inference(forward_demodulation,[],[f94,f78])).

fof(f94,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f93,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f92,f20])).

fof(f92,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f91,f19])).

fof(f91,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f66,f18])).

fof(f66,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f38,f25])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f133,plain,(
    ! [X26] :
      ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X26,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X26,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X26 ) ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,(
    ! [X26] :
      ( sK5 != sK5
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X26,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X26,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X26 ) ),
    inference(superposition,[],[f42,f117])).

fof(f42,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X9 ) ),
    inference(definition_unfolding,[],[f16,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f16,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X9 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f117,plain,(
    ! [X4] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5))
      | k2_mcart_1(k1_mcart_1(sK5)) = X4 ) ),
    inference(forward_demodulation,[],[f106,f78])).

fof(f106,plain,(
    ! [X4] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5))
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f105,f21])).

fof(f105,plain,(
    ! [X4] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5))
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f104,f20])).

% (6011)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f104,plain,(
    ! [X4] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f103,f19])).

fof(f103,plain,(
    ! [X4] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f69,f18])).

fof(f69,plain,(
    ! [X4] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5)),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f35,f25,f40])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(definition_unfolding,[],[f33,f25,f40])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f190,plain,(
    sK4 != k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(superposition,[],[f22,f162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (6016)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (6002)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (6004)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (6012)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (6012)Refutation not found, incomplete strategy% (6012)------------------------------
% 0.20/0.50  % (6012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6009)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (6022)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (6010)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (6017)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (6015)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (6019)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (6012)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6012)Memory used [KB]: 10618
% 0.20/0.51  % (6012)Time elapsed: 0.095 s
% 0.20/0.51  % (6012)------------------------------
% 0.20/0.51  % (6012)------------------------------
% 0.20/0.51  % (6013)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (6016)Refutation not found, incomplete strategy% (6016)------------------------------
% 0.20/0.51  % (6016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6016)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6016)Memory used [KB]: 6140
% 0.20/0.51  % (6016)Time elapsed: 0.005 s
% 0.20/0.51  % (6016)------------------------------
% 0.20/0.51  % (6016)------------------------------
% 0.20/0.51  % (6007)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (6022)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (6010)Refutation not found, incomplete strategy% (6010)------------------------------
% 0.20/0.52  % (6010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6010)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (6010)Memory used [KB]: 10618
% 0.20/0.52  % (6010)Time elapsed: 0.117 s
% 0.20/0.52  % (6010)------------------------------
% 0.20/0.52  % (6010)------------------------------
% 0.20/0.52  % (6005)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (6001)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (6025)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (6020)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (6014)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (6006)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (6030)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.54  % (6001)Refutation not found, incomplete strategy% (6001)------------------------------
% 1.33/0.54  % (6001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (6001)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (6001)Memory used [KB]: 1663
% 1.33/0.54  % (6001)Time elapsed: 0.135 s
% 1.33/0.54  % (6001)------------------------------
% 1.33/0.54  % (6001)------------------------------
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f267,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(subsumption_resolution,[],[f190,f162])).
% 1.33/0.54  fof(f162,plain,(
% 1.33/0.54    ( ! [X0] : (k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f161,f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.33/0.54    inference(flattening,[],[f9])).
% 1.33/0.54  fof(f9,plain,(
% 1.33/0.54    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.33/0.54    inference(ennf_transformation,[],[f8])).
% 1.33/0.54  fof(f8,negated_conjecture,(
% 1.33/0.54    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.33/0.54    inference(negated_conjecture,[],[f7])).
% 1.33/0.54  fof(f7,conjecture,(
% 1.33/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).
% 1.33/0.54  fof(f161,plain,(
% 1.33/0.54    ( ! [X0] : (sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f160,f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    k1_xboole_0 != sK3),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f160,plain,(
% 1.33/0.54    ( ! [X0] : (k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f159,f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    k1_xboole_0 != sK2),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f159,plain,(
% 1.33/0.54    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f158,f19])).
% 1.33/0.54  fof(f19,plain,(
% 1.33/0.54    k1_xboole_0 != sK1),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f158,plain,(
% 1.33/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f157,f18])).
% 1.33/0.54  fof(f18,plain,(
% 1.33/0.54    k1_xboole_0 != sK0),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f157,plain,(
% 1.33/0.54    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(resolution,[],[f151,f41])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 1.33/0.54    inference(definition_unfolding,[],[f17,f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f151,plain,(
% 1.33/0.54    ( ! [X45,X43,X46,X44,X42] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X43,X44,X45),X46)) | k1_xboole_0 = X43 | k1_xboole_0 = X44 | k1_xboole_0 = X45 | k1_xboole_0 = X46 | sK4 = k11_mcart_1(X43,X44,X45,X46,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X42) )),
% 1.33/0.54    inference(superposition,[],[f57,f141])).
% 1.33/0.54  fof(f141,plain,(
% 1.33/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK4) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(duplicate_literal_removal,[],[f138])).
% 1.33/0.54  fof(f138,plain,(
% 1.33/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK4) | k2_mcart_1(k1_mcart_1(sK5)) = X0 | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(superposition,[],[f117,f137])).
% 1.33/0.54  fof(f137,plain,(
% 1.33/0.54    ( ! [X26] : (sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X26) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f136,f112])).
% 1.33/0.54  fof(f112,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 1.33/0.54    inference(forward_demodulation,[],[f90,f78])).
% 1.33/0.54  fof(f78,plain,(
% 1.33/0.54    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 1.33/0.54    inference(subsumption_resolution,[],[f77,f18])).
% 1.33/0.54  fof(f77,plain,(
% 1.33/0.54    k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 1.33/0.54    inference(subsumption_resolution,[],[f76,f21])).
% 1.33/0.54  fof(f76,plain,(
% 1.33/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 1.33/0.54    inference(subsumption_resolution,[],[f75,f20])).
% 1.33/0.54  fof(f75,plain,(
% 1.33/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 1.33/0.54    inference(subsumption_resolution,[],[f62,f19])).
% 1.33/0.54  fof(f62,plain,(
% 1.33/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 1.33/0.54    inference(resolution,[],[f41,f44])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 1.33/0.54    inference(definition_unfolding,[],[f28,f25])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.33/0.54    inference(ennf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 1.33/0.54  fof(f90,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f89,f21])).
% 1.33/0.54  fof(f89,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f88,f20])).
% 1.33/0.54  fof(f88,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f87,f19])).
% 1.33/0.54  fof(f87,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f65,f18])).
% 1.33/0.54  fof(f65,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.33/0.54    inference(resolution,[],[f41,f51])).
% 1.33/0.54  fof(f51,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(definition_unfolding,[],[f39,f25])).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.33/0.54    inference(flattening,[],[f14])).
% 1.33/0.54  fof(f14,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 1.33/0.54  fof(f136,plain,(
% 1.33/0.54    ( ! [X26] : (~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X26) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f135,f116])).
% 1.33/0.54  fof(f116,plain,(
% 1.33/0.54    ( ! [X5] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3) | k2_mcart_1(k1_mcart_1(sK5)) = X5) )),
% 1.33/0.54    inference(forward_demodulation,[],[f110,f78])).
% 1.33/0.54  fof(f110,plain,(
% 1.33/0.54    ( ! [X5] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f109,f21])).
% 1.33/0.54  fof(f109,plain,(
% 1.33/0.54    ( ! [X5] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f108,f20])).
% 1.33/0.54  fof(f108,plain,(
% 1.33/0.54    ( ! [X5] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f107,f19])).
% 1.33/0.54  fof(f107,plain,(
% 1.33/0.54    ( ! [X5] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f70,f18])).
% 1.33/0.54  fof(f70,plain,(
% 1.33/0.54    ( ! [X5] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X5,sK5),sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 1.33/0.54    inference(resolution,[],[f41,f56])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(definition_unfolding,[],[f34,f25])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f135,plain,(
% 1.33/0.54    ( ! [X26] : (~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X26) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f134,f114])).
% 1.33/0.54  fof(f114,plain,(
% 1.33/0.54    ( ! [X2] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2) | k2_mcart_1(k1_mcart_1(sK5)) = X2) )),
% 1.33/0.54    inference(forward_demodulation,[],[f98,f78])).
% 1.33/0.54  fof(f98,plain,(
% 1.33/0.54    ( ! [X2] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f97,f21])).
% 1.33/0.54  fof(f97,plain,(
% 1.33/0.54    ( ! [X2] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f96,f20])).
% 1.33/0.54  fof(f96,plain,(
% 1.33/0.54    ( ! [X2] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f95,f19])).
% 1.33/0.54  fof(f95,plain,(
% 1.33/0.54    ( ! [X2] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f67,f18])).
% 1.33/0.54  fof(f67,plain,(
% 1.33/0.54    ( ! [X2] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X2,sK5),sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 1.33/0.54    inference(resolution,[],[f41,f53])).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(definition_unfolding,[],[f37,f25])).
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f134,plain,(
% 1.33/0.54    ( ! [X26] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X26,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X26) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f133,f113])).
% 1.33/0.54  fof(f113,plain,(
% 1.33/0.54    ( ! [X1] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1) | k2_mcart_1(k1_mcart_1(sK5)) = X1) )),
% 1.33/0.54    inference(forward_demodulation,[],[f94,f78])).
% 1.33/0.54  fof(f94,plain,(
% 1.33/0.54    ( ! [X1] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f93,f21])).
% 1.33/0.54  fof(f93,plain,(
% 1.33/0.54    ( ! [X1] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f92,f20])).
% 1.33/0.54  fof(f92,plain,(
% 1.33/0.54    ( ! [X1] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f91,f19])).
% 1.33/0.54  fof(f91,plain,(
% 1.33/0.54    ( ! [X1] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f66,f18])).
% 1.33/0.54  fof(f66,plain,(
% 1.33/0.54    ( ! [X1] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X1,sK5),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 1.33/0.54    inference(resolution,[],[f41,f52])).
% 1.33/0.54  fof(f52,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(definition_unfolding,[],[f38,f25])).
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f133,plain,(
% 1.33/0.54    ( ! [X26] : (~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X26,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X26,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X26) )),
% 1.33/0.54    inference(trivial_inequality_removal,[],[f123])).
% 1.33/0.54  fof(f123,plain,(
% 1.33/0.54    ( ! [X26] : (sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X26,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X26,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X26,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X26,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X26,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X26) )),
% 1.33/0.54    inference(superposition,[],[f42,f117])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X9) )),
% 1.33/0.54    inference(definition_unfolding,[],[f16,f40])).
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.33/0.54    inference(definition_unfolding,[],[f24,f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X9) )),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f117,plain,(
% 1.33/0.54    ( ! [X4] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5)) | k2_mcart_1(k1_mcart_1(sK5)) = X4) )),
% 1.33/0.54    inference(forward_demodulation,[],[f106,f78])).
% 1.33/0.54  fof(f106,plain,(
% 1.33/0.54    ( ! [X4] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5)) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f105,f21])).
% 1.33/0.54  fof(f105,plain,(
% 1.33/0.54    ( ! [X4] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5)) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f104,f20])).
% 1.33/0.54  % (6011)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.54  fof(f104,plain,(
% 1.33/0.54    ( ! [X4] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f103,f19])).
% 1.33/0.54  fof(f103,plain,(
% 1.33/0.54    ( ! [X4] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f69,f18])).
% 1.33/0.54  fof(f69,plain,(
% 1.33/0.54    ( ! [X4] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X4,sK5),sK7(sK0,sK1,sK2,sK3,X4,sK5)),sK8(sK0,sK1,sK2,sK3,X4,sK5)),sK9(sK0,sK1,sK2,sK3,X4,sK5)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 1.33/0.54    inference(resolution,[],[f41,f55])).
% 1.33/0.54  fof(f55,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5)),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(definition_unfolding,[],[f35,f25,f40])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8) )),
% 1.33/0.54    inference(equality_resolution,[],[f47])).
% 1.33/0.54  fof(f47,plain,(
% 1.33/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 1.33/0.54    inference(definition_unfolding,[],[f33,f25,f40])).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 1.33/0.54    inference(cnf_transformation,[],[f13])).
% 1.33/0.54  fof(f13,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.33/0.54    inference(flattening,[],[f12])).
% 1.33/0.54  fof(f12,plain,(
% 1.33/0.54    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.33/0.54    inference(ennf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 1.33/0.54  fof(f190,plain,(
% 1.33/0.54    sK4 != k2_mcart_1(k1_mcart_1(sK5))),
% 1.33/0.54    inference(superposition,[],[f22,f162])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (6022)------------------------------
% 1.33/0.54  % (6022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (6022)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (6022)Memory used [KB]: 1918
% 1.33/0.54  % (6022)Time elapsed: 0.077 s
% 1.33/0.54  % (6022)------------------------------
% 1.33/0.54  % (6022)------------------------------
% 1.33/0.54  % (6000)Success in time 0.184 s
%------------------------------------------------------------------------------
