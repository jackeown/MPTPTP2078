%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:48 EST 2020

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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
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
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

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
    inference(superposition,[],[f19,f88])).

fof(f88,plain,(
    ! [X24,X23,X21,X25,X22,X20] :
      ( sK4 = k11_mcart_1(X22,X23,X24,X25,X21)
      | k1_xboole_0 = X22
      | k1_xboole_0 = X23
      | k1_xboole_0 = X24
      | k1_xboole_0 = X25
      | ~ m1_subset_1(X21,k4_zfmisc_1(X22,X23,X24,X25))
      | ~ m1_subset_1(X21,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X21) = X20
      | sK5 != X21 ) ),
    inference(superposition,[],[f34,f83])).

fof(f83,plain,(
    ! [X4,X5] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4
      | sK5 != X5 ) ),
    inference(subsumption_resolution,[],[f82,f18])).

fof(f82,plain,(
    ! [X4,X5] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4
      | sK5 != X5 ) ),
    inference(subsumption_resolution,[],[f81,f17])).

fof(f81,plain,(
    ! [X4,X5] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4
      | sK5 != X5 ) ),
    inference(subsumption_resolution,[],[f80,f16])).

fof(f80,plain,(
    ! [X4,X5] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4
      | sK5 != X5 ) ),
    inference(subsumption_resolution,[],[f66,f15])).

fof(f66,plain,(
    ! [X4,X5] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4
      | sK5 != X5 ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X4,X5] :
      ( k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4
      | sK5 != X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4 ) ),
    inference(superposition,[],[f29,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0)
      | sK5 != X0
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f61,f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f59,f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f58,f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0)
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
      | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0)
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
      | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 ) ),
    inference(subsumption_resolution,[],[f55,f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f54,f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f53,f16])).

% (14444)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0)
      | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0)
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
      | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0)
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
      | sK4 = sK9(X0,X1,sK2,sK3,X2,X3)
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
      | sK4 = sK9(X0,X1,sK2,sK3,X2,X3)
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
      | sK4 = sK9(X0,X1,sK2,sK3,X2,X3)
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
      | sK4 = sK9(X0,X1,sK2,sK3,X2,X3)
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
      | sK4 = sK9(X0,X1,X2,sK3,X3,X4)
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
      | sK4 = sK9(X0,X1,X2,sK3,X3,X4)
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
      | sK4 = sK9(X0,X1,X2,sK3,X3,X4)
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
      | sK4 = sK9(X0,X1,X2,X3,X4,X5)
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
      | sK4 = X9 ) ),
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

fof(f34,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
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
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f160,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f19,f120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (14433)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (14439)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (14434)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (14427)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (14429)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (14431)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14427)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f160,f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X0,X1] : (X0 = X1) )),
% 0.21/0.49    inference(superposition,[],[f120,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X15] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X15] : (~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    k1_xboole_0 != sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X15] : (k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    k1_xboole_0 != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X15] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f116,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X15] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X15] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X15] : (sK4 != sK4 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 | sK5 != sK5) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X15] : (sK4 != sK4 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X15 | sK5 != sK5) )),
% 0.21/0.49    inference(superposition,[],[f19,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X24,X23,X21,X25,X22,X20] : (sK4 = k11_mcart_1(X22,X23,X24,X25,X21) | k1_xboole_0 = X22 | k1_xboole_0 = X23 | k1_xboole_0 = X24 | k1_xboole_0 = X25 | ~m1_subset_1(X21,k4_zfmisc_1(X22,X23,X24,X25)) | ~m1_subset_1(X21,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X21) = X20 | sK5 != X21) )),
% 0.21/0.49    inference(superposition,[],[f34,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4 | sK5 != X5) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f18])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4 | sK5 != X5) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f81,f17])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4 | sK5 != X5) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f16])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4 | sK5 != X5) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f66,f15])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4 | sK5 != X5) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X4,X5),sK7(sK0,sK1,sK2,sK3,X4,X5),sK8(sK0,sK1,sK2,sK3,X4,X5),sK4) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4 | sK5 != X5 | ~m1_subset_1(X5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X5) = X4) )),
% 0.21/0.49    inference(superposition,[],[f29,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0) | sK5 != X0 | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f61,f18])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f60,f17])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f59,f16])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f58,f15])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK5 != X0 | sK4 = sK9(sK0,sK1,sK2,sK3,X1,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1 | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,X0) = X1) )),
% 0.21/0.50    inference(resolution,[],[f56,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK5 != X0 | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f55,f18])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f54,f17])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f53,f16])).
% 0.21/0.50  % (14444)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X2,X0),sK0) | sK4 = sK9(X1,sK1,sK2,sK3,X2,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2 | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(X1,sK1,sK2,sK3,X0) = X2) )),
% 0.21/0.50    inference(resolution,[],[f51,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK9(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f50,f18])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK9(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f49,f17])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK9(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 | k1_xboole_0 = sK3) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2,X3),sK0) | sK4 = sK9(X0,X1,sK2,sK3,X2,X3) | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2 | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,sK2,sK3,X3) = X2) )),
% 0.21/0.50    inference(resolution,[],[f47,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | ~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK9(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK9(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3,X4),sK0) | sK4 = sK9(X0,X1,X2,sK3,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | k8_mcart_1(X0,X1,X2,sK3,X4) = X3) )),
% 0.21/0.50    inference(resolution,[],[f44,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),sK3) | ~m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),sK1) | ~m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),sK2) | sK5 != X5 | ~m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),sK0) | sK4 = sK9(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.50    inference(superposition,[],[f13,f29])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X9) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.50    inference(equality_resolution,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.50    inference(superposition,[],[f19,f120])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (14427)------------------------------
% 0.21/0.50  % (14427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14427)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (14427)Memory used [KB]: 10746
% 0.21/0.50  % (14427)Time elapsed: 0.080 s
% 0.21/0.50  % (14427)------------------------------
% 0.21/0.50  % (14427)------------------------------
% 0.21/0.50  % (14440)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (14425)Success in time 0.143 s
%------------------------------------------------------------------------------
