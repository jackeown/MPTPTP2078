%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 704 expanded)
%              Number of leaves         :    5 ( 128 expanded)
%              Depth                    :   43
%              Number of atoms          :  484 (5819 expanded)
%              Number of equality atoms :  358 (3627 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(subsumption_resolution,[],[f173,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

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
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
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
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f173,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f172,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f172,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f171,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f171,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f170,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f170,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f169,f19])).

fof(f19,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f169,plain,
    ( sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f157,f14])).

fof(f14,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f157,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK5,k4_zfmisc_1(X8,X9,X10,X11))
      | sK4 = k10_mcart_1(X8,X9,X10,X11,sK5)
      | k1_xboole_0 = X8
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11 ) ),
    inference(backward_demodulation,[],[f92,f155])).

fof(f155,plain,(
    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f154,f15])).

fof(f154,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f153,f14])).

fof(f153,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f152,f18])).

fof(f152,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f151,f17])).

fof(f151,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f150,f16])).

fof(f150,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f145,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f145,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f144,f15])).

fof(f144,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f143,f14])).

fof(f143,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f142,f18])).

fof(f142,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f141,f17])).

fof(f141,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f140,f16])).

fof(f140,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f139,f132])).

fof(f132,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) ),
    inference(subsumption_resolution,[],[f131,f15])).

fof(f131,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f130,f14])).

fof(f130,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f129,f18])).

fof(f129,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f128,f17])).

fof(f128,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f127,f16])).

fof(f127,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f122])).

fof(f122,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(forward_demodulation,[],[f121,f80])).

fof(f80,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f79,f15])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f78,f18])).

fof(f78,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f77,f17])).

fof(f77,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f72,f16])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(resolution,[],[f22,f14])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f121,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f120,f18])).

fof(f120,plain,
    ( k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f119,f17])).

fof(f119,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f118,f16])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f117,f15])).

fof(f117,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5) ),
    inference(resolution,[],[f91,f14])).

fof(f91,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK5,k4_zfmisc_1(X4,X5,X6,X7))
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | sK7(sK0,sK1,sK2,sK3,sK5) = k9_mcart_1(X4,X5,X6,X7,sK5) ) ),
    inference(superposition,[],[f42,f89])).

fof(f89,plain,(
    sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f88,f15])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f87,f18])).

fof(f87,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f86,f17])).

fof(f86,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f81,f16])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(resolution,[],[f35,f14])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f10])).

% (32147)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f42,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X6 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(definition_unfolding,[],[f31,f20])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
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

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f139,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f126,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f126,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f124,f110])).

fof(f110,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) ),
    inference(subsumption_resolution,[],[f109,f15])).

fof(f109,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f108,f14])).

fof(f108,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f107,f18])).

fof(f107,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f106,f17])).

fof(f106,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f105,f16])).

fof(f105,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f29,f101])).

fof(f101,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(forward_demodulation,[],[f100,f71])).

fof(f71,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f70,f15])).

fof(f70,plain,
    ( k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f69,f18])).

fof(f69,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f63,f16])).

fof(f63,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(resolution,[],[f21,f14])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f99,f18])).

fof(f99,plain,
    ( k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f98,f17])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f97,f16])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f96,f15])).

fof(f96,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(resolution,[],[f90,f14])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | sK6(sK0,sK1,sK2,sK3,sK5) = k8_mcart_1(X0,X1,X2,X3,sK5) ) ),
    inference(superposition,[],[f43,f89])).

fof(f43,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X5 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(definition_unfolding,[],[f30,f20])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f124,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(backward_demodulation,[],[f102,f122])).

fof(f102,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(backward_demodulation,[],[f95,f101])).

fof(f95,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f34,f89])).

fof(f34,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X8 ) ),
    inference(definition_unfolding,[],[f13,f20])).

fof(f13,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X8 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f92,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK5,k4_zfmisc_1(X8,X9,X10,X11))
      | k1_xboole_0 = X8
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | sK8(sK0,sK1,sK2,sK3,sK5) = k10_mcart_1(X8,X9,X10,X11,sK5) ) ),
    inference(superposition,[],[f41,f89])).

fof(f41,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X7 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(definition_unfolding,[],[f32,f20])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:47:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (32150)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (32162)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (32150)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (32167)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f173,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    k1_xboole_0 != sK3),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f5])).
% 0.22/0.54  fof(f5,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    k1_xboole_0 = sK3),
% 0.22/0.54    inference(subsumption_resolution,[],[f172,f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    k1_xboole_0 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 0.22/0.54    inference(subsumption_resolution,[],[f171,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 0.22/0.54    inference(subsumption_resolution,[],[f170,f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 0.22/0.54    inference(resolution,[],[f157,f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK5,k4_zfmisc_1(X8,X9,X10,X11)) | sK4 = k10_mcart_1(X8,X9,X10,X11,sK5) | k1_xboole_0 = X8 | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11) )),
% 0.22/0.54    inference(backward_demodulation,[],[f92,f155])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f154,f15])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f153,f14])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f152,f18])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f151,f17])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f150,f16])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f145,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f15])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f143,f14])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f142,f18])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f17])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f140,f16])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f139,f132])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f131,f15])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f130,f14])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f129,f18])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f128,f17])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f127,f16])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(superposition,[],[f28,f122])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(forward_demodulation,[],[f121,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f79,f15])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f78,f18])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f77,f17])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f72,f16])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(resolution,[],[f22,f14])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f120,f18])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f119,f17])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f118,f16])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f117,f15])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(resolution,[],[f91,f14])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK5,k4_zfmisc_1(X4,X5,X6,X7)) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k1_xboole_0 = X6 | k1_xboole_0 = X7 | sK7(sK0,sK1,sK2,sK3,sK5) = k9_mcart_1(X4,X5,X6,X7,sK5)) )),
% 0.22/0.54    inference(superposition,[],[f42,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.54    inference(subsumption_resolution,[],[f88,f15])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.54    inference(subsumption_resolution,[],[f87,f18])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.54    inference(subsumption_resolution,[],[f86,f17])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.54    inference(subsumption_resolution,[],[f81,f16])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.54    inference(resolution,[],[f35,f14])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  % (32147)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X6) )),
% 0.22/0.54    inference(equality_resolution,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f20])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f126,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f124,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f109,f15])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f108,f14])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f107,f18])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f106,f17])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f105,f16])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(superposition,[],[f29,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(forward_demodulation,[],[f100,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f70,f15])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f69,f18])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f68,f17])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f63,f16])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(resolution,[],[f21,f14])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f99,f18])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f98,f17])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f97,f16])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f96,f15])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(resolution,[],[f90,f14])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | sK6(sK0,sK1,sK2,sK3,sK5) = k8_mcart_1(X0,X1,X2,X3,sK5)) )),
% 0.22/0.54    inference(superposition,[],[f43,f89])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X5) )),
% 0.22/0.54    inference(equality_resolution,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f20])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ~m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(backward_demodulation,[],[f102,f122])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ~m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(backward_demodulation,[],[f95,f101])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(superposition,[],[f34,f89])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X8) )),
% 0.22/0.54    inference(definition_unfolding,[],[f13,f20])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X8) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK5,k4_zfmisc_1(X8,X9,X10,X11)) | k1_xboole_0 = X8 | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11 | sK8(sK0,sK1,sK2,sK3,sK5) = k10_mcart_1(X8,X9,X10,X11,sK5)) )),
% 0.22/0.54    inference(superposition,[],[f41,f89])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X7) )),
% 0.22/0.54    inference(equality_resolution,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.22/0.54    inference(definition_unfolding,[],[f32,f20])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (32150)------------------------------
% 0.22/0.54  % (32150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32150)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (32150)Memory used [KB]: 6524
% 0.22/0.54  % (32150)Time elapsed: 0.102 s
% 0.22/0.54  % (32150)------------------------------
% 0.22/0.54  % (32150)------------------------------
% 0.22/0.55  % (32143)Success in time 0.174 s
%------------------------------------------------------------------------------
