%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 (1865 expanded)
%              Number of leaves         :    6 ( 397 expanded)
%              Depth                    :   28
%              Number of atoms          :  440 (12781 expanded)
%              Number of equality atoms :  331 (8113 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f203])).

fof(f203,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f133,f133])).

fof(f133,plain,(
    ! [X0] : k2_mcart_1(k1_mcart_1(sK5)) = X0 ),
    inference(subsumption_resolution,[],[f132,f21])).

fof(f21,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f132,plain,(
    ! [X0] :
      ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f131,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f131,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f130,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f130,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f129,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f129,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(subsumption_resolution,[],[f128,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f128,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(resolution,[],[f126,f39])).

fof(f39,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f16,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f126,plain,(
    ! [X19,X17,X15,X18,X16] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18),X19))
      | k1_xboole_0 = X16
      | k1_xboole_0 = X17
      | k1_xboole_0 = X18
      | k1_xboole_0 = X19
      | sK4 = k11_mcart_1(X16,X17,X18,X19,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X15 ) ),
    inference(superposition,[],[f54,f122])).

fof(f122,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(superposition,[],[f108,f118])).

fof(f118,plain,(
    ! [X20] :
      ( sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X20 ) ),
    inference(subsumption_resolution,[],[f117,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(forward_demodulation,[],[f83,f68])).

fof(f68,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f67,f17])).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f66,f20])).

fof(f66,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f65,f19])).

fof(f65,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f64,f18])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(resolution,[],[f41,f39])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f82,f20])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f81,f19])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f80,f18])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f17])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f117,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X20 ) ),
    inference(subsumption_resolution,[],[f116,f102])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(forward_demodulation,[],[f101,f68])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f100,f20])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f99,f19])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f98,f18])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f97,f17])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X20 ) ),
    inference(subsumption_resolution,[],[f115,f96])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(forward_demodulation,[],[f95,f68])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f20])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f93,f19])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f92,f18])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f91,f17])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f115,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X20 ) ),
    inference(subsumption_resolution,[],[f114,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(forward_demodulation,[],[f89,f68])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f88,f20])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f87,f19])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f18])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f85,f17])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f114,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X20 ) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,(
    ! [X20] :
      ( sK5 != sK5
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(sK5)) = X20 ) ),
    inference(superposition,[],[f15,f108])).

fof(f15,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X9 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f108,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k2_mcart_1(k1_mcart_1(sK5)) = X0 ) ),
    inference(forward_demodulation,[],[f107,f68])).

fof(f107,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f106,f20])).

fof(f106,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f19])).

fof(f105,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f104,f18])).

fof(f104,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f103,f17])).

fof(f103,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f206,plain,(
    sK4 != k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(superposition,[],[f21,f133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (22429)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (22413)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (22408)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (22405)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (22409)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (22426)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (22421)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (22418)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (22421)Refutation not found, incomplete strategy% (22421)------------------------------
% 0.22/0.53  % (22421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22414)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (22415)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (22424)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (22421)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22421)Memory used [KB]: 10618
% 0.22/0.53  % (22421)Time elapsed: 0.107 s
% 0.22/0.53  % (22421)------------------------------
% 0.22/0.53  % (22421)------------------------------
% 0.22/0.53  % (22420)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (22410)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (22404)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (22417)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (22413)Refutation not found, incomplete strategy% (22413)------------------------------
% 0.22/0.54  % (22413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22413)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22413)Memory used [KB]: 10874
% 0.22/0.54  % (22413)Time elapsed: 0.102 s
% 0.22/0.54  % (22413)------------------------------
% 0.22/0.54  % (22413)------------------------------
% 0.22/0.54  % (22404)Refutation not found, incomplete strategy% (22404)------------------------------
% 0.22/0.54  % (22404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22404)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22404)Memory used [KB]: 1791
% 0.22/0.54  % (22404)Time elapsed: 0.116 s
% 0.22/0.54  % (22404)------------------------------
% 0.22/0.54  % (22404)------------------------------
% 0.22/0.54  % (22416)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (22433)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (22432)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (22419)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (22428)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (22422)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (22407)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (22406)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (22425)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (22427)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (22410)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f206,f203])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    ( ! [X0,X1] : (X0 = X1) )),
% 0.22/0.55    inference(superposition,[],[f133,f133])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ( ! [X0] : (k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f132,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.55    inference(flattening,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.55    inference(negated_conjecture,[],[f6])).
% 0.22/0.55  fof(f6,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ( ! [X0] : (sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    k1_xboole_0 != sK3),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f130,f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    k1_xboole_0 != sK2),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f129,f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f128,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    k1_xboole_0 != sK0),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(resolution,[],[f126,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.22/0.55    inference(definition_unfolding,[],[f16,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    ( ! [X19,X17,X15,X18,X16] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18),X19)) | k1_xboole_0 = X16 | k1_xboole_0 = X17 | k1_xboole_0 = X18 | k1_xboole_0 = X19 | sK4 = k11_mcart_1(X16,X17,X18,X19,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X15) )),
% 0.22/0.55    inference(superposition,[],[f54,f122])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4) | k2_mcart_1(k1_mcart_1(sK5)) = X0 | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(superposition,[],[f108,f118])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    ( ! [X20] : (sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X20) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f117,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f83,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.22/0.55    inference(subsumption_resolution,[],[f67,f17])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.22/0.55    inference(subsumption_resolution,[],[f66,f20])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.22/0.55    inference(subsumption_resolution,[],[f65,f19])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.22/0.55    inference(subsumption_resolution,[],[f64,f18])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.22/0.55    inference(resolution,[],[f41,f39])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f26,f38])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f82,f20])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f81,f19])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f80,f18])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f79,f17])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(resolution,[],[f48,f39])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(definition_unfolding,[],[f37,f38])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.55    inference(flattening,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X8 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    ( ! [X20] : (~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X20) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f116,f102])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f101,f68])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f100,f20])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f99,f19])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f98,f18])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f97,f17])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(resolution,[],[f53,f39])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(definition_unfolding,[],[f32,f38])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X20] : (~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X20) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f115,f96])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f95,f68])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f94,f20])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f93,f19])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f92,f18])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f91,f17])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(resolution,[],[f50,f39])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(definition_unfolding,[],[f35,f38])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ( ! [X20] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X20) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f114,f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f89,f68])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f88,f20])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f87,f19])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f86,f18])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f85,f17])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(resolution,[],[f49,f39])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(definition_unfolding,[],[f36,f38])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ( ! [X20] : (~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X20) )),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f113])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    ( ! [X20] : (sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(sK5)) = X20) )),
% 0.22/0.55    inference(superposition,[],[f15,f108])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X9) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k2_mcart_1(k1_mcart_1(sK5)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f107,f68])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f106,f20])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f105,f19])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f104,f18])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f103,f17])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.55    inference(resolution,[],[f52,f39])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(definition_unfolding,[],[f33,f38])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8) )),
% 0.22/0.55    inference(equality_resolution,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.22/0.55    inference(definition_unfolding,[],[f31,f38])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.55    inference(flattening,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    sK4 != k2_mcart_1(k1_mcart_1(sK5))),
% 0.22/0.55    inference(superposition,[],[f21,f133])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (22410)------------------------------
% 0.22/0.55  % (22410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22410)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (22410)Memory used [KB]: 6396
% 0.22/0.55  % (22410)Time elapsed: 0.095 s
% 0.22/0.55  % (22410)------------------------------
% 0.22/0.55  % (22410)------------------------------
% 0.22/0.55  % (22403)Success in time 0.181 s
%------------------------------------------------------------------------------
