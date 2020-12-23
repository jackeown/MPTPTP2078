%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0890+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 19.31s
% Output     : Refutation 19.31s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 116 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :   78 ( 426 expanded)
%              Number of equality atoms :   68 ( 368 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21212,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20949,f21211])).

fof(f21211,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f21210,f5989])).

fof(f5989,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(superposition,[],[f2312,f4818])).

fof(f4818,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4817,f2279])).

fof(f2279,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1368])).

fof(f1368,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != k2_mcart_1(X3)
            | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3))
            | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1346])).

fof(f1346,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                  & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                  & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1345])).

fof(f1345,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f4817,plain,
    ( k1_xboole_0 = sK2
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4816,f2278])).

fof(f2278,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1368])).

fof(f4816,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4748,f2277])).

fof(f2277,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1368])).

fof(f4748,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f3865,f3873])).

fof(f3873,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(definition_unfolding,[],[f2287,f2414,f2638])).

fof(f2638,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f2414,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f2287,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f1372])).

fof(f1372,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1342])).

fof(f1342,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f3865,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f2276,f2414])).

fof(f2276,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1368])).

fof(f2312,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1349])).

fof(f1349,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f21210,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) ),
    inference(trivial_inequality_removal,[],[f21155])).

fof(f21155,plain,
    ( k1_mcart_1(k1_mcart_1(sK3)) != k1_mcart_1(k1_mcart_1(sK3))
    | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) ),
    inference(backward_demodulation,[],[f2275,f20948])).

fof(f20948,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f2311,f5988])).

fof(f5988,plain,(
    k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f2311,f4818])).

fof(f2311,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1349])).

fof(f2275,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))
    | k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) ),
    inference(cnf_transformation,[],[f1368])).

fof(f20949,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f2312,f5988])).
%------------------------------------------------------------------------------
