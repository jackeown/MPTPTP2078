%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 353 expanded)
%              Number of leaves         :    8 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  305 (2271 expanded)
%              Number of equality atoms :  208 (1390 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f94,plain,(
    sK4 != k2_mcart_1(sK5) ),
    inference(superposition,[],[f20,f61])).

fof(f61,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f60,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f59,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f58,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f49,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f38,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f15,f37])).

fof(f15,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f107,plain,(
    sK4 = k2_mcart_1(sK5) ),
    inference(forward_demodulation,[],[f99,f104])).

fof(f104,plain,(
    sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f103,f77])).

fof(f77,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f76,f16])).

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f75,f19])).

fof(f75,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f74,f18])).

fof(f74,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f53,f17])).

fof(f53,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f103,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f102,f93])).

fof(f93,plain,(
    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f92,f16])).

fof(f92,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f91,f19])).

fof(f91,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f90,f18])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f57,f17])).

fof(f57,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f101,f85])).

fof(f85,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f84,f16])).

fof(f84,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f83,f19])).

fof(f83,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f82,f18])).

fof(f82,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f55,f17])).

fof(f55,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f100,f81])).

fof(f81,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f80,f16])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f79,f19])).

fof(f79,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f78,f18])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f54,f17])).

fof(f54,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(resolution,[],[f38,f45])).

% (17223)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (17219)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f100,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f39,f89])).

fof(f89,plain,(
    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f88,f16])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f87,f19])).

fof(f87,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f86,f18])).

fof(f86,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f56,f17])).

fof(f56,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(resolution,[],[f38,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(definition_unfolding,[],[f32,f37,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X9 ) ),
    inference(definition_unfolding,[],[f14,f36])).

fof(f14,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X9 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    k2_mcart_1(sK5) = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f22,f89])).

fof(f22,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (17226)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (17239)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (17232)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (17225)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (17224)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (17239)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    sK4 != k2_mcart_1(sK5)),
% 0.21/0.52    inference(superposition,[],[f20,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f60,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f59,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.21/0.52    inference(resolution,[],[f38,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.52    inference(definition_unfolding,[],[f15,f37])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    sK4 = k2_mcart_1(sK5)),
% 0.21/0.52    inference(forward_demodulation,[],[f99,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f16])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f19])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f74,f18])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f17])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    inference(resolution,[],[f38,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f37])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f92,f16])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f91,f19])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f18])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f57,f17])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.52    inference(resolution,[],[f38,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f31,f37])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f16])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f83,f19])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f18])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f17])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.52    inference(resolution,[],[f38,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f37])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f100,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f16])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f19])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f18])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f54,f17])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.52    inference(resolution,[],[f38,f45])).
% 0.21/0.52  % (17223)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (17219)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f37])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(superposition,[],[f39,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    inference(subsumption_resolution,[],[f88,f16])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    inference(subsumption_resolution,[],[f87,f19])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    inference(subsumption_resolution,[],[f86,f18])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    inference(subsumption_resolution,[],[f56,f17])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    inference(resolution,[],[f38,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f37,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X9) )),
% 0.21/0.52    inference(definition_unfolding,[],[f14,f36])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X9) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    k2_mcart_1(sK5) = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(superposition,[],[f22,f89])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (17239)------------------------------
% 0.21/0.52  % (17239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17239)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (17239)Memory used [KB]: 1791
% 0.21/0.52  % (17239)Time elapsed: 0.070 s
% 0.21/0.52  % (17239)------------------------------
% 0.21/0.52  % (17239)------------------------------
% 0.21/0.53  % (17217)Success in time 0.169 s
%------------------------------------------------------------------------------
