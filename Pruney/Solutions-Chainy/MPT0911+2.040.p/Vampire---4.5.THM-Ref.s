%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 (1217 expanded)
%              Number of leaves         :    6 ( 250 expanded)
%              Depth                    :   25
%              Number of atoms          :  326 (7559 expanded)
%              Number of equality atoms :  240 (4869 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(subsumption_resolution,[],[f163,f159])).

fof(f159,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f111,f111])).

fof(f111,plain,(
    ! [X0] : k2_mcart_1(k1_mcart_1(sK4)) = X0 ),
    inference(subsumption_resolution,[],[f110,f20])).

fof(f20,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f110,plain,(
    ! [X0] :
      ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f109,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f108,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f108,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f107,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(resolution,[],[f101,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f16,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11))
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | sK3 = k7_mcart_1(X9,X10,X11,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X8 ) ),
    inference(superposition,[],[f47,f98])).

fof(f98,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK3)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK3)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(superposition,[],[f82,f94])).

fof(f94,plain,(
    ! [X12] :
      ( sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f93,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f66,f58])).

fof(f58,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f57,f17])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f56,f19])).

fof(f56,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f55,f18])).

fof(f55,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f37,f34])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f65,f19])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f64,f18])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f63,f17])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f33,f22])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X6
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X6
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f93,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f92,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f76,f58])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f75,f19])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f74,f18])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f73,f17])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f29,f22])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f91,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f71,f58])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f70,f19])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f69,f18])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f32,f22])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,(
    ! [X12] :
      ( sK4 != sK4
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | k2_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(superposition,[],[f35,f82])).

fof(f35,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f15,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k2_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f81,f58])).

fof(f81,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f80,f19])).

fof(f80,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f18])).

fof(f79,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f78,f17])).

fof(f78,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)),sK7(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f30,f22,f21])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X6 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k7_mcart_1(X0,X1,X2,X3) = X6 ) ),
    inference(definition_unfolding,[],[f28,f22,f21])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k3_mcart_1(X4,X5,X6) != X3
      | k7_mcart_1(X0,X1,X2,X3) = X6 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f163,plain,(
    sK3 != k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f20,f111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 21:02:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (17631)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.47  % (17647)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.48  % (17631)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f163,f159])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ( ! [X0,X1] : (X0 = X1) )),
% 0.22/0.48    inference(superposition,[],[f111,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X0] : (k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f110,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ( ! [X0] : (sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f109,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    k1_xboole_0 != sK2),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = sK2 | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    k1_xboole_0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f107,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    k1_xboole_0 != sK0),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(resolution,[],[f101,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.48    inference(definition_unfolding,[],[f16,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11)) | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11 | sK3 = k7_mcart_1(X9,X10,X11,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X8) )),
% 0.22/0.48    inference(superposition,[],[f47,f98])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK3) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK3) | k2_mcart_1(k1_mcart_1(sK4)) = X0 | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(superposition,[],[f82,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X12] : (sK3 = sK7(sK0,sK1,sK2,X12,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f93,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.48    inference(forward_demodulation,[],[f66,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.22/0.48    inference(subsumption_resolution,[],[f57,f17])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.22/0.48    inference(subsumption_resolution,[],[f56,f19])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.22/0.48    inference(subsumption_resolution,[],[f55,f18])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.22/0.48    inference(resolution,[],[f37,f34])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f24,f22])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f65,f19])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f64,f18])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f63,f17])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(resolution,[],[f42,f34])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(definition_unfolding,[],[f33,f22])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X5] : (? [X6] : (? [X7] : (X3 != X6 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X5] : (? [X6] : (? [X7] : ((X3 != X6 & k3_mcart_1(X5,X6,X7) = X4) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0))) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X12] : (~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK7(sK0,sK1,sK2,X12,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.49    inference(forward_demodulation,[],[f76,f58])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f19])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f74,f18])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f73,f17])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(resolution,[],[f46,f34])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(definition_unfolding,[],[f29,f22])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X12] : (~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK7(sK0,sK1,sK2,X12,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.49    inference(forward_demodulation,[],[f71,f58])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f70,f19])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f18])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f17])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(resolution,[],[f43,f34])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(definition_unfolding,[],[f32,f22])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ( ! [X12] : (~m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK7(sK0,sK1,sK2,X12,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X12] : (sK4 != sK4 | ~m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK7(sK0,sK1,sK2,X12,sK4) | k2_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.22/0.49    inference(superposition,[],[f35,f82])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 0.22/0.49    inference(definition_unfolding,[],[f15,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k2_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.22/0.49    inference(forward_demodulation,[],[f81,f58])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f80,f19])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f79,f18])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f78,f17])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.22/0.49    inference(resolution,[],[f45,f34])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)),sK7(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(definition_unfolding,[],[f30,f22,f21])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X6) )),
% 0.22/0.49    inference(equality_resolution,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k7_mcart_1(X0,X1,X2,X3) = X6) )),
% 0.22/0.49    inference(definition_unfolding,[],[f28,f22,f21])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k3_mcart_1(X4,X5,X6) != X3 | k7_mcart_1(X0,X1,X2,X3) = X6) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    sK3 != k2_mcart_1(k1_mcart_1(sK4))),
% 0.22/0.49    inference(superposition,[],[f20,f111])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (17631)------------------------------
% 0.22/0.49  % (17631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17631)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (17631)Memory used [KB]: 6268
% 0.22/0.49  % (17631)Time elapsed: 0.077 s
% 0.22/0.49  % (17631)------------------------------
% 0.22/0.49  % (17631)------------------------------
% 0.22/0.49  % (17624)Success in time 0.122 s
%------------------------------------------------------------------------------
