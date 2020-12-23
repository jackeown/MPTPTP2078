%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 356 expanded)
%              Number of leaves         :    7 (  80 expanded)
%              Depth                    :   23
%              Number of atoms          :  321 (2292 expanded)
%              Number of equality atoms :  221 (1408 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f152,f17])).

fof(f17,plain,(
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

fof(f152,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f151,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f151,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f150,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f149,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f149,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f148,f21])).

fof(f21,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f148,plain,
    ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f126,f41])).

fof(f41,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f16,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f126,plain,(
    ! [X35,X33,X36,X34] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36))
      | sK4 = k11_mcart_1(X33,X34,X35,X36,sK5)
      | k1_xboole_0 = X34
      | k1_xboole_0 = X35
      | k1_xboole_0 = X36
      | k1_xboole_0 = X33 ) ),
    inference(backward_demodulation,[],[f114,f125])).

fof(f125,plain,(
    sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f124,f64])).

fof(f64,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f63,f17])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f62,f20])).

fof(f62,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f61,f19])).

fof(f61,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f60,f18])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f34,plain,(
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

fof(f124,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f123,f79])).

fof(f79,plain,(
    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f78,f17])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f77,f20])).

fof(f77,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f76,f19])).

fof(f76,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f75,f18])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(resolution,[],[f51,f41])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f122,f74])).

fof(f74,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f73,f17])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f72,f20])).

fof(f72,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f71,f19])).

fof(f71,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f121,f69])).

fof(f69,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f67,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f66,f19])).

fof(f66,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f65,f18])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f42,f105])).

fof(f105,plain,(
    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f104,f17])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f103,f20])).

fof(f103,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f102,f19])).

fof(f102,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f101,f18])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(definition_unfolding,[],[f31,f40,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X9 ) ),
    inference(definition_unfolding,[],[f15,f39])).

fof(f15,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X9 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f114,plain,(
    ! [X35,X33,X36,X34] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36))
      | k1_xboole_0 = X34
      | k1_xboole_0 = X35
      | k1_xboole_0 = X36
      | k1_xboole_0 = X33
      | sK9(sK0,sK1,sK2,sK3,sK5) = k11_mcart_1(X33,X34,X35,X36,sK5) ) ),
    inference(superposition,[],[f56,f105])).

fof(f56,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(definition_unfolding,[],[f38,f40,f39])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (13617)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (13622)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (13633)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (13614)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (13614)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (13617)Refutation not found, incomplete strategy% (13617)------------------------------
% 0.22/0.56  % (13617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13625)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (13630)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (13625)Refutation not found, incomplete strategy% (13625)------------------------------
% 0.22/0.57  % (13625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (13625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (13625)Memory used [KB]: 10618
% 0.22/0.57  % (13625)Time elapsed: 0.148 s
% 0.22/0.57  % (13625)------------------------------
% 0.22/0.57  % (13625)------------------------------
% 0.22/0.58  % (13617)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (13617)Memory used [KB]: 10874
% 0.22/0.58  % (13617)Time elapsed: 0.130 s
% 0.22/0.58  % (13617)------------------------------
% 0.22/0.58  % (13617)------------------------------
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f153,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f152,f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    k1_xboole_0 != sK0),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.58    inference(flattening,[],[f10])).
% 0.22/0.58  fof(f10,plain,(
% 0.22/0.58    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.58    inference(negated_conjecture,[],[f8])).
% 0.22/0.58  fof(f8,conjecture,(
% 0.22/0.58    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).
% 0.22/0.58  fof(f152,plain,(
% 0.22/0.58    k1_xboole_0 = sK0),
% 0.22/0.58    inference(subsumption_resolution,[],[f151,f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    k1_xboole_0 != sK3),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f151,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 0.22/0.58    inference(subsumption_resolution,[],[f150,f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    k1_xboole_0 != sK2),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f150,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 0.22/0.58    inference(subsumption_resolution,[],[f149,f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    k1_xboole_0 != sK1),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f149,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 0.22/0.58    inference(subsumption_resolution,[],[f148,f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 0.22/0.58    inference(resolution,[],[f126,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.22/0.58    inference(definition_unfolding,[],[f16,f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f25,f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f126,plain,(
% 0.22/0.58    ( ! [X35,X33,X36,X34] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36)) | sK4 = k11_mcart_1(X33,X34,X35,X36,sK5) | k1_xboole_0 = X34 | k1_xboole_0 = X35 | k1_xboole_0 = X36 | k1_xboole_0 = X33) )),
% 0.22/0.58    inference(backward_demodulation,[],[f114,f125])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f124,f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f63,f17])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f62,f20])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f61,f19])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f60,f18])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.58    inference(resolution,[],[f47,f41])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f34,f40])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.22/0.58  fof(f124,plain,(
% 0.22/0.58    ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f123,f79])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f78,f17])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f77,f20])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f76,f19])).
% 0.22/0.58  fof(f76,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f75,f18])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.22/0.58    inference(resolution,[],[f51,f41])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f30,f40])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f122,f74])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f73,f17])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f72,f20])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f71,f19])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f70,f18])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.22/0.58    inference(resolution,[],[f49,f41])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f32,f40])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f121,f69])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f68,f17])).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f67,f20])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f66,f19])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f65,f18])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.22/0.58    inference(resolution,[],[f48,f41])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f33,f40])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f121,plain,(
% 0.22/0.58    ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f115])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.58    inference(superposition,[],[f42,f105])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.58    inference(subsumption_resolution,[],[f104,f17])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.58    inference(subsumption_resolution,[],[f103,f20])).
% 0.22/0.58  fof(f103,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.58    inference(subsumption_resolution,[],[f102,f19])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.58    inference(subsumption_resolution,[],[f101,f18])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.58    inference(resolution,[],[f50,f41])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.22/0.58    inference(definition_unfolding,[],[f31,f40,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f24,f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X9) )),
% 0.22/0.58    inference(definition_unfolding,[],[f15,f39])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X9) )),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f114,plain,(
% 0.22/0.58    ( ! [X35,X33,X36,X34] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36)) | k1_xboole_0 = X34 | k1_xboole_0 = X35 | k1_xboole_0 = X36 | k1_xboole_0 = X33 | sK9(sK0,sK1,sK2,sK3,sK5) = k11_mcart_1(X33,X34,X35,X36,sK5)) )),
% 0.22/0.58    inference(superposition,[],[f56,f105])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8) )),
% 0.22/0.58    inference(equality_resolution,[],[f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.22/0.58    inference(definition_unfolding,[],[f38,f40,f39])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (13614)------------------------------
% 0.22/0.58  % (13614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (13614)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (13614)Memory used [KB]: 6396
% 0.22/0.58  % (13614)Time elapsed: 0.134 s
% 0.22/0.58  % (13614)------------------------------
% 0.22/0.58  % (13614)------------------------------
% 0.22/0.58  % (13607)Success in time 0.216 s
%------------------------------------------------------------------------------
