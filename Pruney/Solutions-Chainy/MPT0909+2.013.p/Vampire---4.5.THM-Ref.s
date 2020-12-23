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
% DateTime   : Thu Dec  3 12:59:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 372 expanded)
%              Number of leaves         :    5 (  80 expanded)
%              Depth                    :   29
%              Number of atoms          :  241 (2230 expanded)
%              Number of equality atoms :  151 (1400 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(subsumption_resolution,[],[f92,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f92,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f26,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f12,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f12,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f90,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f89,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f88,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f21,f18])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK6(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f88,plain,(
    ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(subsumption_resolution,[],[f87,f13])).

fof(f87,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f86,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f85,f15])).

fof(f85,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f84,f14])).

fof(f84,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f83,f70])).

fof(f70,plain,(
    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f69,f13])).

fof(f69,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f68,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f67,f15])).

fof(f67,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f66,f14])).

fof(f66,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f57])).

fof(f57,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f56,f13])).

fof(f56,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f55,f15])).

fof(f55,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f54,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(X0,X1,X2,sK4) ) ),
    inference(superposition,[],[f37,f44])).

fof(f44,plain,(
    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f43,f13])).

fof(f43,plain,
    ( k1_xboole_0 = sK0
    | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f42,f15])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f38,f14])).

fof(f38,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(resolution,[],[f30,f26])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3 ) ),
    inference(definition_unfolding,[],[f20,f18,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X4 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k5_mcart_1(X0,X1,X2,X3) = X4 ) ),
    inference(definition_unfolding,[],[f23,f18,f17])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(X4,X5,X6) != X3
      | k5_mcart_1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK5(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f65,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f64,f16])).

fof(f16,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    inference(forward_demodulation,[],[f62,f57])).

fof(f62,plain,
    ( ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | sK3 = sK5(sK0,sK1,sK2,sK4) ),
    inference(backward_demodulation,[],[f53,f57])).

fof(f53,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)
    | sK3 = sK5(sK0,sK1,sK2,sK4) ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)
    | sK3 = sK5(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f27,f44])).

fof(f27,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X5 ) ),
    inference(definition_unfolding,[],[f11,f17])).

fof(f11,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X5 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (4057)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (4074)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (4056)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (4066)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (4061)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (4062)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (4072)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (4058)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (4051)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (4051)Refutation not found, incomplete strategy% (4051)------------------------------
% 0.21/0.52  % (4051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4051)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4051)Memory used [KB]: 1791
% 0.21/0.52  % (4051)Time elapsed: 0.115 s
% 0.21/0.52  % (4051)------------------------------
% 0.21/0.52  % (4051)------------------------------
% 0.21/0.52  % (4076)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (4064)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (4068)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (4052)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (4077)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (4059)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (4068)Refutation not found, incomplete strategy% (4068)------------------------------
% 0.21/0.52  % (4068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4057)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f92,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f91,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.52    inference(definition_unfolding,[],[f12,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f90,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f89,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f88,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f18])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK6(X0,X1,X2,X3),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f13])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f86,f26])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f85,f15])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f14])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f69,f13])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f68,f26])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f67,f15])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f66,f14])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(superposition,[],[f28,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f56,f13])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f55,f15])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f54,f14])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(resolution,[],[f45,f26])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(X0,X1,X2,sK4)) )),
% 0.21/0.53    inference(superposition,[],[f37,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f43,f13])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f42,f15])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f38,f14])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.53    inference(resolution,[],[f30,f26])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f18,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X4) )),
% 0.21/0.53    inference(equality_resolution,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k5_mcart_1(X0,X1,X2,X3) = X4) )),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f18,f17])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(X4,X5,X6) != X3 | k5_mcart_1(X0,X1,X2,X3) = X4) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (! [X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(? [X3] : (? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f18])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK5(X0,X1,X2,X3),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f65,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f18])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK7(X0,X1,X2,X3),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f64,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    sK3 = k5_mcart_1(sK0,sK1,sK2,sK4) | ~m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f62,f57])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | sK3 = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(backward_demodulation,[],[f53,f57])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) | sK3 = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    sK4 != sK4 | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) | sK3 = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(superposition,[],[f27,f44])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X5) )),
% 0.21/0.53    inference(definition_unfolding,[],[f11,f17])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X5) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4057)------------------------------
% 0.21/0.53  % (4057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4057)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4057)Memory used [KB]: 6396
% 0.21/0.53  % (4057)Time elapsed: 0.120 s
% 0.21/0.53  % (4057)------------------------------
% 0.21/0.53  % (4057)------------------------------
% 0.21/0.53  % (4050)Success in time 0.172 s
%------------------------------------------------------------------------------
