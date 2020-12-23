%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 512 expanded)
%              Number of leaves         :    3 (  85 expanded)
%              Depth                    :   40
%              Number of atoms          :  440 (4846 expanded)
%              Number of equality atoms :  319 (3037 expanded)
%              Maximal formula depth    :   23 (  11 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(subsumption_resolution,[],[f160,f156])).

fof(f156,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f120,f120])).

fof(f120,plain,(
    ! [X15] : k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 ),
    inference(subsumption_resolution,[],[f119,f14])).

fof(f14,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f119,plain,(
    ! [X15] :
      ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 ) ),
    inference(subsumption_resolution,[],[f118,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f7])).

fof(f118,plain,(
    ! [X15] :
      ( k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 ) ),
    inference(subsumption_resolution,[],[f117,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f117,plain,(
    ! [X15] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 ) ),
    inference(subsumption_resolution,[],[f116,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f116,plain,(
    ! [X15] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 ) ),
    inference(subsumption_resolution,[],[f96,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X15] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 ) ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,(
    ! [X15] :
      ( sK4 != sK4
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15
      | sK5 != sK5 ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X15] :
      ( sK4 != sK4
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15
      | sK5 != sK5 ) ),
    inference(superposition,[],[f19,f87])).

fof(f87,plain,(
    ! [X14,X19,X17,X15,X18,X16] :
      ( sK4 = k10_mcart_1(X16,X17,X18,X19,X15)
      | k1_xboole_0 = X16
      | k1_xboole_0 = X17
      | k1_xboole_0 = X18
      | k1_xboole_0 = X19
      | ~ m1_subset_1(X15,k4_zfmisc_1(X16,X17,X18,X19))
      | ~ m1_subset_1(X15,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X15) = X14
      | sK5 != X15 ) ),
    inference(superposition,[],[f35,f71])).

fof(f71,plain,(
    ! [X2,X3] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2
      | sK5 != X3 ) ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f70,plain,(
    ! [X2,X3] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2
      | sK5 != X3 ) ),
    inference(subsumption_resolution,[],[f69,f17])).

fof(f69,plain,(
    ! [X2,X3] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2
      | sK5 != X3 ) ),
    inference(subsumption_resolution,[],[f68,f16])).

fof(f68,plain,(
    ! [X2,X3] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2
      | sK5 != X3 ) ),
    inference(subsumption_resolution,[],[f67,f15])).

fof(f67,plain,(
    ! [X2,X3] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2
      | sK5 != X3 ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X2,X3] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2
      | sK5 != X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2 ) ),
    inference(superposition,[],[f29,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | sK5 != X0
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f61,f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f59,f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f58,f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 ) ),
    inference(resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK5 != X0
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 ) ),
    inference(subsumption_resolution,[],[f55,f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f54,f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 ) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2,X3)
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2,X3)
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f49,f17])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2,X3)
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2,X3)
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 ) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2)
      | ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k8_mcart_1(X0,X1,X2,sK3,X4) = X3 ) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | k8_mcart_1(X0,X1,X2,sK3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | k8_mcart_1(X0,X1,X2,sK3,X4) = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | k8_mcart_1(X0,X1,X2,sK3,X4) = X3 ) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),sK3)
      | ~ m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),sK2)
      | sK5 != X5
      | ~ m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),sK0)
      | sK4 = sK8(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(superposition,[],[f13,f29])).

fof(f13,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X8 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f19,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f160,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f19,f120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (22022)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (22008)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (22007)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (22013)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (22021)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (22017)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (22020)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (22010)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (22009)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (22006)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (22005)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (22016)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (22024)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (22012)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (22013)Refutation not found, incomplete strategy% (22013)------------------------------
% 0.21/0.50  % (22013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22013)Memory used [KB]: 6396
% 0.21/0.50  % (22013)Time elapsed: 0.089 s
% 0.21/0.50  % (22013)------------------------------
% 0.21/0.50  % (22013)------------------------------
% 0.21/0.50  % (22019)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (22014)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (22003)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (22011)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (22004)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (22015)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (22015)Refutation not found, incomplete strategy% (22015)------------------------------
% 0.21/0.51  % (22015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22015)Memory used [KB]: 6140
% 0.21/0.51  % (22015)Time elapsed: 0.003 s
% 0.21/0.51  % (22015)------------------------------
% 0.21/0.51  % (22015)------------------------------
% 0.21/0.51  % (22023)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (22004)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f156])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1) )),
% 0.21/0.52    inference(superposition,[],[f120,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ( ! [X15] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X15] : (~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X15] : (k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X15] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f116,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ( ! [X15] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X15] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X15] : (sK4 != sK4 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 | sK5 != sK5) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X15] : (sK4 != sK4 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 | sK5 != sK5) )),
% 0.21/0.52    inference(superposition,[],[f19,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X14,X19,X17,X15,X18,X16] : (sK4 = k10_mcart_1(X16,X17,X18,X19,X15) | k1_xboole_0 = X16 | k1_xboole_0 = X17 | k1_xboole_0 = X18 | k1_xboole_0 = X19 | ~m1_subset_1(X15,k4_zfmisc_1(X16,X17,X18,X19)) | ~m1_subset_1(X15,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X15) = X14 | sK5 != X15) )),
% 0.21/0.52    inference(superposition,[],[f35,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2 | sK5 != X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f18])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2 | sK5 != X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f17])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2 | sK5 != X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f16])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2 | sK5 != X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f67,f15])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2 | sK5 != X3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X2,X3),sK7(sK0,sK1,sK2,sK3,X2,X3),sK4,sK9(sK0,sK1,sK2,sK3,X2,X3)) = X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2 | sK5 != X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X3) = X2) )),
% 0.21/0.52    inference(superposition,[],[f29,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | sK5 != X0 | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f61,f18])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f60,f17])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f59,f16])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f15])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1) )),
% 0.21/0.52    inference(resolution,[],[f56,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK5 != X0 | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f18])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f54,f17])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f16])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2) )),
% 0.21/0.52    inference(resolution,[],[f51,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f50,f18])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f17])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2) )),
% 0.21/0.52    inference(resolution,[],[f47,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | ~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.52    inference(resolution,[],[f44,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),sK3) | ~m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),sK1) | ~m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),sK2) | sK5 != X5 | ~m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),sK0) | sK4 = sK8(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.52    inference(superposition,[],[f13,f29])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X8) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(superposition,[],[f19,f120])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22004)------------------------------
% 0.21/0.52  % (22004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22004)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22004)Memory used [KB]: 10746
% 0.21/0.52  % (22004)Time elapsed: 0.108 s
% 0.21/0.52  % (22004)------------------------------
% 0.21/0.52  % (22004)------------------------------
% 0.21/0.52  % (22002)Success in time 0.163 s
%------------------------------------------------------------------------------
