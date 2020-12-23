%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   68 (36245 expanded)
%              Number of leaves         :   10 (13559 expanded)
%              Depth                    :   25
%              Number of atoms          :  235 (270470 expanded)
%              Number of equality atoms :  221 (237926 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f977,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f430,f668,f665])).

fof(f665,plain,(
    ! [X8,X9] :
      ( k1_mcart_1(sK4) != k4_tarski(X8,X9)
      | k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))) ) ),
    inference(backward_demodulation,[],[f352,f664])).

fof(f664,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(forward_demodulation,[],[f645,f429])).

fof(f429,plain,(
    k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(forward_demodulation,[],[f403,f379])).

fof(f379,plain,(
    k1_mcart_1(sK4) = k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(backward_demodulation,[],[f82,f378])).

fof(f378,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f366,f82])).

fof(f366,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4))) ),
    inference(unit_resulting_resolution,[],[f82,f349])).

fof(f349,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != k1_mcart_1(sK4)
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(superposition,[],[f45,f82])).

fof(f45,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK6(X0,X1) != X1
              & k4_tarski(sK5(X0,X1),sK6(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK6(X0,X1) != X1
        & k4_tarski(sK5(X0,X1),sK6(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

fof(f82,plain,(
    k1_mcart_1(sK4) = k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(forward_demodulation,[],[f77,f66])).

fof(f66,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    inference(backward_demodulation,[],[f50,f65])).

fof(f65,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(forward_demodulation,[],[f60,f50])).

fof(f60,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))) ),
    inference(unit_resulting_resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK4
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(superposition,[],[f45,f50])).

fof(f50,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f29,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f29,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) )
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f28,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)) = k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))) ),
    inference(unit_resulting_resolution,[],[f66,f59])).

fof(f59,plain,(
    ! [X10,X11] :
      ( sK4 != k4_tarski(X10,X11)
      | k1_mcart_1(k4_tarski(X10,X11)) = X10 ) ),
    inference(superposition,[],[f49,f50])).

fof(f49,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK7(X0,X1) != X1
              & k4_tarski(sK7(X0,X1),sK8(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK7(X0,X1) != X1
        & k4_tarski(sK7(X0,X1),sK8(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f403,plain,(
    k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)) = k1_mcart_1(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(k1_mcart_1(sK4)))) ),
    inference(unit_resulting_resolution,[],[f379,f353])).

fof(f353,plain,(
    ! [X10,X11] :
      ( k1_mcart_1(sK4) != k4_tarski(X10,X11)
      | k1_mcart_1(k4_tarski(X10,X11)) = X10 ) ),
    inference(superposition,[],[f49,f82])).

fof(f645,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4))) ),
    inference(unit_resulting_resolution,[],[f429,f626])).

fof(f626,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != k1_mcart_1(k1_mcart_1(sK4))
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(superposition,[],[f45,f429])).

fof(f352,plain,(
    ! [X8,X9] :
      ( k1_mcart_1(sK4) != k4_tarski(X8,X9)
      | k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)) ) ),
    inference(superposition,[],[f49,f82])).

fof(f668,plain,(
    ! [X4,X5] : k4_tarski(X4,X5) != k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_subsumption,[],[f383,f629,f664])).

fof(f629,plain,(
    ! [X8,X9] :
      ( k1_mcart_1(k1_mcart_1(sK4)) != k4_tarski(X8,X9)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ) ),
    inference(superposition,[],[f49,f429])).

fof(f383,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f382,f65])).

fof(f382,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) != k2_mcart_1(k1_mcart_1(sK4))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(backward_demodulation,[],[f30,f378])).

fof(f30,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(cnf_transformation,[],[f16])).

fof(f430,plain,(
    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(backward_demodulation,[],[f379,f429])).

%------------------------------------------------------------------------------
