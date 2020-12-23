%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 678 expanded)
%              Number of leaves         :   12 ( 260 expanded)
%              Depth                    :   24
%              Number of atoms          :  388 (5019 expanded)
%              Number of equality atoms :  319 (4194 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(subsumption_resolution,[],[f168,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) )
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4)
              | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4))
              | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
              | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( ( k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4)
            | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4)
            | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4)
            | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4) )
          & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X4] :
        ( ( k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4)
          | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4)
          | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4)
          | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4) )
        & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) )
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4)
            | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4))
            | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f168,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f167,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f167,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f166,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f166,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f165,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f165,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f164,f163])).

fof(f163,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f157,f162])).

fof(f162,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f161,f20])).

fof(f161,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f160,f21])).

fof(f160,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f159,f22])).

fof(f159,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f158,f23])).

fof(f158,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f125,f24])).

fof(f24,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f125,plain,(
    ! [X26,X24,X27,X25] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X24,X25,X26,X27))
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = k9_mcart_1(X24,X25,X26,X27,sK4)
      | k1_xboole_0 = X27
      | k1_xboole_0 = X26
      | k1_xboole_0 = X25
      | k1_xboole_0 = X24 ) ),
    inference(backward_demodulation,[],[f63,f120])).

fof(f120,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f31,f97])).

fof(f97,plain,(
    k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[],[f30,f71])).

fof(f71,plain,(
    k1_mcart_1(sK4) = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[],[f30,f57])).

fof(f57,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f56,f20])).

fof(f56,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f55,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f54,f22])).

fof(f54,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f49,f23])).

fof(f49,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f11,f18,f17,f16,f15])).

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
                    ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3) ) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f30,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X26,X24,X27,X25] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X24,X25,X26,X27))
      | sK6(sK0,sK1,sK2,sK3,sK4) = k9_mcart_1(X24,X25,X26,X27,sK4)
      | k1_xboole_0 = X27
      | k1_xboole_0 = X26
      | k1_xboole_0 = X25
      | k1_xboole_0 = X24 ) ),
    inference(superposition,[],[f47,f57])).

fof(f47,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f157,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f151,f156])).

fof(f156,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f155,f20])).

fof(f155,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f154,f21])).

fof(f154,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f153,f22])).

fof(f153,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f152,f23])).

fof(f152,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f101,f24])).

fof(f101,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X28,X29,X30,X31))
      | k2_mcart_1(k1_mcart_1(sK4)) = k10_mcart_1(X28,X29,X30,X31,sK4)
      | k1_xboole_0 = X31
      | k1_xboole_0 = X30
      | k1_xboole_0 = X29
      | k1_xboole_0 = X28 ) ),
    inference(backward_demodulation,[],[f64,f96])).

fof(f96,plain,(
    k2_mcart_1(k1_mcart_1(sK4)) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f31,f71])).

fof(f64,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X28,X29,X30,X31))
      | sK7(sK0,sK1,sK2,sK3,sK4) = k10_mcart_1(X28,X29,X30,X31,sK4)
      | k1_xboole_0 = X31
      | k1_xboole_0 = X30
      | k1_xboole_0 = X29
      | k1_xboole_0 = X28 ) ),
    inference(superposition,[],[f46,f57])).

fof(f46,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f151,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f25,f150])).

fof(f150,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f149,f20])).

fof(f149,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f148,f21])).

fof(f148,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f147,f22])).

fof(f147,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f146,f23])).

fof(f146,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f73,f24])).

fof(f73,plain,(
    ! [X35,X33,X34,X32] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X32,X33,X34,X35))
      | k2_mcart_1(sK4) = k11_mcart_1(X32,X33,X34,X35,sK4)
      | k1_xboole_0 = X35
      | k1_xboole_0 = X34
      | k1_xboole_0 = X33
      | k1_xboole_0 = X32 ) ),
    inference(backward_demodulation,[],[f65,f70])).

fof(f70,plain,(
    k2_mcart_1(sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f31,f57])).

fof(f65,plain,(
    ! [X35,X33,X34,X32] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X32,X33,X34,X35))
      | sK8(sK0,sK1,sK2,sK3,sK4) = k11_mcart_1(X32,X33,X34,X35,sK4)
      | k1_xboole_0 = X35
      | k1_xboole_0 = X34
      | k1_xboole_0 = X33
      | k1_xboole_0 = X32 ) ),
    inference(superposition,[],[f45,f57])).

fof(f45,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(cnf_transformation,[],[f14])).

fof(f164,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f129,f24])).

fof(f129,plain,(
    ! [X23,X21,X22,X20] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X20,X21,X22,X23))
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = k8_mcart_1(X20,X21,X22,X23,sK4)
      | k1_xboole_0 = X23
      | k1_xboole_0 = X22
      | k1_xboole_0 = X21
      | k1_xboole_0 = X20 ) ),
    inference(backward_demodulation,[],[f62,f121])).

fof(f121,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f30,f97])).

fof(f62,plain,(
    ! [X23,X21,X22,X20] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X20,X21,X22,X23))
      | sK5(sK0,sK1,sK2,sK3,sK4) = k8_mcart_1(X20,X21,X22,X23,sK4)
      | k1_xboole_0 = X23
      | k1_xboole_0 = X22
      | k1_xboole_0 = X21
      | k1_xboole_0 = X20 ) ),
    inference(superposition,[],[f48,f57])).

fof(f48,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (10910)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (10923)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (10910)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (10911)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (10921)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f168,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4) | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))) & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4) | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X4] : ((k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4) | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X4] : ((k2_mcart_1(X4) != k11_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK0,sK1,sK2,sK3,X4) | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK0,sK1,sK2,sK3,X4) | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK0,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4) | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))) & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4) | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f167,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f166,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f165,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f157,f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f161,f20])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f21])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f22])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f23])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f125,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X26,X24,X27,X25] : (~m1_subset_1(sK4,k4_zfmisc_1(X24,X25,X26,X27)) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = k9_mcart_1(X24,X25,X26,X27,sK4) | k1_xboole_0 = X27 | k1_xboole_0 = X26 | k1_xboole_0 = X25 | k1_xboole_0 = X24) )),
% 0.21/0.52    inference(backward_demodulation,[],[f63,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = sK6(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.52    inference(superposition,[],[f31,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.52    inference(superposition,[],[f30,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_mcart_1(sK4) = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.52    inference(superposition,[],[f30,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.52    inference(subsumption_resolution,[],[f56,f20])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f21])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f54,f22])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f23])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4)),sK7(sK0,sK1,sK2,sK3,sK4)),sK8(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f44,f24])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_tarski(k4_tarski(k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f36,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f37,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f11,f18,f17,f16,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X26,X24,X27,X25] : (~m1_subset_1(sK4,k4_zfmisc_1(X24,X25,X26,X27)) | sK6(sK0,sK1,sK2,sK3,sK4) = k9_mcart_1(X24,X25,X26,X27,sK4) | k1_xboole_0 = X27 | k1_xboole_0 = X26 | k1_xboole_0 = X25 | k1_xboole_0 = X24) )),
% 0.21/0.52    inference(superposition,[],[f47,f57])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f39])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f151,f156])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.52    inference(subsumption_resolution,[],[f155,f20])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f154,f21])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f153,f22])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f23])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f101,f24])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X30,X28,X31,X29] : (~m1_subset_1(sK4,k4_zfmisc_1(X28,X29,X30,X31)) | k2_mcart_1(k1_mcart_1(sK4)) = k10_mcart_1(X28,X29,X30,X31,sK4) | k1_xboole_0 = X31 | k1_xboole_0 = X30 | k1_xboole_0 = X29 | k1_xboole_0 = X28) )),
% 0.21/0.52    inference(backward_demodulation,[],[f64,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    k2_mcart_1(k1_mcart_1(sK4)) = sK7(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.52    inference(superposition,[],[f31,f71])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X30,X28,X31,X29] : (~m1_subset_1(sK4,k4_zfmisc_1(X28,X29,X30,X31)) | sK7(sK0,sK1,sK2,sK3,sK4) = k10_mcart_1(X28,X29,X30,X31,sK4) | k1_xboole_0 = X31 | k1_xboole_0 = X30 | k1_xboole_0 = X29 | k1_xboole_0 = X28) )),
% 0.21/0.52    inference(superposition,[],[f46,f57])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f39])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f25,f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f149,f20])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f148,f21])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f22])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f23])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f73,f24])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X35,X33,X34,X32] : (~m1_subset_1(sK4,k4_zfmisc_1(X32,X33,X34,X35)) | k2_mcart_1(sK4) = k11_mcart_1(X32,X33,X34,X35,sK4) | k1_xboole_0 = X35 | k1_xboole_0 = X34 | k1_xboole_0 = X33 | k1_xboole_0 = X32) )),
% 0.21/0.52    inference(backward_demodulation,[],[f65,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    k2_mcart_1(sK4) = sK8(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.52    inference(superposition,[],[f31,f57])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X35,X33,X34,X32] : (~m1_subset_1(sK4,k4_zfmisc_1(X32,X33,X34,X35)) | sK8(sK0,sK1,sK2,sK3,sK4) = k11_mcart_1(X32,X33,X34,X35,sK4) | k1_xboole_0 = X35 | k1_xboole_0 = X34 | k1_xboole_0 = X33 | k1_xboole_0 = X32) )),
% 0.21/0.52    inference(superposition,[],[f45,f57])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f39])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4) | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f129,f24])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X23,X21,X22,X20] : (~m1_subset_1(sK4,k4_zfmisc_1(X20,X21,X22,X23)) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = k8_mcart_1(X20,X21,X22,X23,sK4) | k1_xboole_0 = X23 | k1_xboole_0 = X22 | k1_xboole_0 = X21 | k1_xboole_0 = X20) )),
% 0.21/0.52    inference(backward_demodulation,[],[f62,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) = sK5(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.52    inference(superposition,[],[f30,f97])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X23,X21,X22,X20] : (~m1_subset_1(sK4,k4_zfmisc_1(X20,X21,X22,X23)) | sK5(sK0,sK1,sK2,sK3,sK4) = k8_mcart_1(X20,X21,X22,X23,sK4) | k1_xboole_0 = X23 | k1_xboole_0 = X22 | k1_xboole_0 = X21 | k1_xboole_0 = X20) )),
% 0.21/0.52    inference(superposition,[],[f48,f57])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f39])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (10910)------------------------------
% 0.21/0.52  % (10910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10910)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (10910)Memory used [KB]: 6652
% 0.21/0.52  % (10910)Time elapsed: 0.076 s
% 0.21/0.52  % (10910)------------------------------
% 0.21/0.52  % (10910)------------------------------
% 0.21/0.53  % (10904)Success in time 0.166 s
%------------------------------------------------------------------------------
