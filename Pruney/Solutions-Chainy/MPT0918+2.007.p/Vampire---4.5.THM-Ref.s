%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 (1258 expanded)
%              Number of leaves         :   10 ( 411 expanded)
%              Depth                    :   20
%              Number of atoms          :  305 (11170 expanded)
%              Number of equality atoms :  262 (10169 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f106,f113,f115,f117])).

fof(f117,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f45,f108])).

fof(f108,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    inference(backward_demodulation,[],[f67,f101])).

fof(f101,plain,(
    sK8 = k2_mcart_1(sK4) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,
    ( sK4 != sK4
    | sK8 = k2_mcart_1(sK4) ),
    inference(superposition,[],[f78,f88])).

fof(f88,plain,(
    sK4 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f87,f55])).

fof(f55,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f54,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
    & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5,X6,X7,X8] :
            ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
              | k10_mcart_1(X0,X1,X2,X3,X4) != X7
              | k9_mcart_1(X0,X1,X2,X3,X4) != X6
              | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( ? [X8,X7,X6,X5] :
          ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
            | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
            | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
            | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X8,X7,X6,X5] :
        ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
          | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
          | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
          | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
        & k4_mcart_1(X5,X6,X7,X8) = sK4 )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
      & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f54,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f52,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f47,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
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

fof(f14,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f86,f59])).

fof(f59,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f58,f15])).

fof(f58,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f57,f16])).

fof(f57,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f56,f17])).

fof(f56,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f48,f18])).

fof(f48,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f85,f63])).

fof(f63,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f62,f15])).

fof(f62,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f61,f16])).

fof(f61,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f60,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f49,f18])).

fof(f49,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f71,f67])).

fof(f71,plain,(
    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f70,f15])).

fof(f70,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f69,f16])).

fof(f69,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f51,f18])).

fof(f51,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f78,plain,(
    ! [X26,X24,X27,X25] :
      ( sK4 != k4_mcart_1(X24,X25,X26,X27)
      | sK8 = X27 ) ),
    inference(superposition,[],[f29,f19])).

fof(f19,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X3 = X7 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f67,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f66,f15])).

fof(f66,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f65,f16])).

fof(f65,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f17])).

fof(f64,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f50,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | spl9_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl9_4
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f115,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl9_3 ),
    inference(subsumption_resolution,[],[f41,f109])).

fof(f109,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 ),
    inference(backward_demodulation,[],[f63,f102])).

fof(f102,plain,(
    sK7 = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( sK4 != sK4
    | sK7 = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f76,f88])).

fof(f76,plain,(
    ! [X19,X17,X18,X16] :
      ( sK4 != k4_mcart_1(X16,X17,X18,X19)
      | sK7 = X18 ) ),
    inference(superposition,[],[f28,f19])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X2 = X6 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | spl9_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl9_3
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f113,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl9_2 ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f37,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | spl9_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl9_2
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f110,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 ),
    inference(backward_demodulation,[],[f59,f103])).

fof(f103,plain,(
    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( sK4 != sK4
    | sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f74,f88])).

fof(f74,plain,(
    ! [X10,X8,X11,X9] :
      ( sK4 != k4_mcart_1(X8,X9,X10,X11)
      | sK6 = X9 ) ),
    inference(superposition,[],[f27,f19])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X1 = X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f106,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f104,f84])).

fof(f84,plain,
    ( sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | spl9_1 ),
    inference(superposition,[],[f33,f55])).

fof(f33,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5
    | spl9_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl9_1
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f104,plain,(
    sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( sK4 != sK4
    | sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f72,f88])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != sK4
      | sK5 = X0 ) ),
    inference(superposition,[],[f26,f19])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f20,f43,f39,f35,f31])).

fof(f20,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (14258)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (14258)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (14274)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f46,f106,f113,f115,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl9_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    $false | spl9_4),
% 0.21/0.47    inference(subsumption_resolution,[],[f45,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8),
% 0.21/0.47    inference(backward_demodulation,[],[f67,f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    sK8 = k2_mcart_1(sK4)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    sK4 != sK4 | sK8 = k2_mcart_1(sK4)),
% 0.21/0.47    inference(superposition,[],[f78,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))),
% 0.21/0.47    inference(forward_demodulation,[],[f87,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f54,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f12,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) => (? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) => ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4] : ((? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f53,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f52,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    k1_xboole_0 != sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f47,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k1_xboole_0 != sK3),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(resolution,[],[f14,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))),
% 0.21/0.47    inference(forward_demodulation,[],[f86,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f58,f15])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f16])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f17])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f48,f18])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(resolution,[],[f14,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))),
% 0.21/0.47    inference(forward_demodulation,[],[f85,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f15])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f61,f16])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f60,f17])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f49,f18])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(resolution,[],[f14,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(sK4))),
% 0.21/0.47    inference(forward_demodulation,[],[f71,f67])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.47    inference(subsumption_resolution,[],[f70,f15])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f16])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f17])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f51,f18])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(resolution,[],[f14,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (! [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X26,X24,X27,X25] : (sK4 != k4_mcart_1(X24,X25,X26,X27) | sK8 = X27) )),
% 0.21/0.47    inference(superposition,[],[f29,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X3 = X7) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f66,f15])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f16])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f17])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f18])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.47    inference(resolution,[],[f14,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | spl9_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl9_4 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl9_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    $false | spl9_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f41,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7),
% 0.21/0.47    inference(backward_demodulation,[],[f63,f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    sK7 = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    sK4 != sK4 | sK7 = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.47    inference(superposition,[],[f76,f88])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X19,X17,X18,X16] : (sK4 != k4_mcart_1(X16,X17,X18,X19) | sK7 = X18) )),
% 0.21/0.47    inference(superposition,[],[f28,f19])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X2 = X6) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | spl9_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl9_3 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl9_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    $false | spl9_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | spl9_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl9_2 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6),
% 0.21/0.47    inference(backward_demodulation,[],[f59,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    sK4 != sK4 | sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.47    inference(superposition,[],[f74,f88])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X10,X8,X11,X9] : (sK4 != k4_mcart_1(X8,X9,X10,X11) | sK6 = X9) )),
% 0.21/0.47    inference(superposition,[],[f27,f19])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X1 = X5) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl9_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    $false | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | spl9_1),
% 0.21/0.47    inference(superposition,[],[f33,f55])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 | spl9_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    spl9_1 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    sK4 != sK4 | sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.47    inference(superposition,[],[f72,f88])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != sK4 | sK5 = X0) )),
% 0.21/0.47    inference(superposition,[],[f26,f19])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X0 = X4) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f43,f39,f35,f31])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (14258)------------------------------
% 0.21/0.47  % (14258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14258)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (14258)Memory used [KB]: 10618
% 0.21/0.47  % (14258)Time elapsed: 0.067 s
% 0.21/0.47  % (14258)------------------------------
% 0.21/0.47  % (14258)------------------------------
% 0.21/0.48  % (14256)Success in time 0.12 s
%------------------------------------------------------------------------------
