%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 520 expanded)
%              Number of leaves         :   10 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          :  207 (2041 expanded)
%              Number of equality atoms :  159 (1725 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f47])).

% (6859)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f47,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f141,plain,(
    ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f126,f137])).

fof(f137,plain,(
    sK3 = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f135,f47])).

% (6857)Refutation not found, incomplete strategy% (6857)------------------------------
% (6857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6857)Termination reason: Refutation not found, incomplete strategy

% (6857)Memory used [KB]: 10746
% (6857)Time elapsed: 0.147 s
% (6857)------------------------------
% (6857)------------------------------
fof(f135,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | sK3 = k2_mcart_1(sK3) ),
    inference(superposition,[],[f123,f134])).

fof(f134,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f133,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f124,f101])).

fof(f101,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f94,f85])).

fof(f85,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f79,f72])).

fof(f72,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f67,f17])).

fof(f17,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f67,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f66,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f65,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f62,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f79,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f78,f19])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f77,f21])).

fof(f77,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f74,f20])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f36,f29])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f93,f19])).

fof(f93,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f92,f21])).

fof(f92,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f89,f20])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,(
    ~ r1_tarski(k1_tarski(k2_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3)) ),
    inference(superposition,[],[f59,f115])).

fof(f115,plain,(
    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f114,f94])).

fof(f114,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f113,f79])).

fof(f113,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f112,f67])).

fof(f112,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f111,f19])).

fof(f111,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f110,f21])).

% (6864)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f110,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f107,f20])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f43,f38])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f59,plain,(
    ! [X4,X5,X3] : ~ r1_tarski(k1_tarski(X4),k1_tarski(k3_mcart_1(X3,X4,X5))) ),
    inference(subsumption_resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f23,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f53,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_tarski(X4),k1_tarski(k3_mcart_1(X3,X4,X5)))
      | k1_xboole_0 = k1_tarski(X4) ) ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(X2,X0),X1))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f123,plain,(
    ~ r1_tarski(k1_tarski(k1_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3)) ),
    inference(superposition,[],[f58,f115])).

fof(f58,plain,(
    ! [X2,X0,X1] : ~ r1_tarski(k1_tarski(X0),k1_tarski(k3_mcart_1(X0,X1,X2))) ),
    inference(subsumption_resolution,[],[f52,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(k3_mcart_1(X0,X1,X2)))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f42,f39])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f29])).

% (6864)Refutation not found, incomplete strategy% (6864)------------------------------
% (6864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f126,plain,(
    ~ r1_tarski(k1_tarski(k2_mcart_1(sK3)),k1_tarski(sK3)) ),
    inference(superposition,[],[f61,f115])).

fof(f61,plain,(
    ! [X14,X15,X16] : ~ r1_tarski(k1_tarski(X16),k1_tarski(k3_mcart_1(X14,X15,X16))) ),
    inference(subsumption_resolution,[],[f56,f49])).

fof(f56,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k1_tarski(X16),k1_tarski(k3_mcart_1(X14,X15,X16)))
      | k1_xboole_0 = k1_tarski(X16) ) ),
    inference(superposition,[],[f25,f39])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (6869)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (6856)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (6861)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (6880)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (6861)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % (6857)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f148,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(subsumption_resolution,[],[f141,f47])).
% 1.45/0.57  % (6859)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.57  fof(f47,plain,(
% 1.45/0.57    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 1.45/0.57    inference(equality_resolution,[],[f28])).
% 1.45/0.57  fof(f28,plain,(
% 1.45/0.57    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 1.45/0.57  fof(f141,plain,(
% 1.45/0.57    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3))),
% 1.45/0.57    inference(backward_demodulation,[],[f126,f137])).
% 1.45/0.57  fof(f137,plain,(
% 1.45/0.57    sK3 = k2_mcart_1(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f135,f47])).
% 1.45/0.57  % (6857)Refutation not found, incomplete strategy% (6857)------------------------------
% 1.45/0.57  % (6857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (6857)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (6857)Memory used [KB]: 10746
% 1.45/0.57  % (6857)Time elapsed: 0.147 s
% 1.45/0.57  % (6857)------------------------------
% 1.45/0.57  % (6857)------------------------------
% 1.45/0.57  fof(f135,plain,(
% 1.45/0.57    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | sK3 = k2_mcart_1(sK3)),
% 1.45/0.57    inference(superposition,[],[f123,f134])).
% 1.45/0.57  fof(f134,plain,(
% 1.45/0.57    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f133,f47])).
% 1.45/0.57  fof(f133,plain,(
% 1.45/0.57    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | sK3 = k2_mcart_1(sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(superposition,[],[f124,f101])).
% 1.45/0.57  fof(f101,plain,(
% 1.45/0.57    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(superposition,[],[f94,f85])).
% 1.45/0.57  fof(f85,plain,(
% 1.45/0.57    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(superposition,[],[f79,f72])).
% 1.45/0.57  fof(f72,plain,(
% 1.45/0.57    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.45/0.57    inference(superposition,[],[f67,f17])).
% 1.45/0.57  fof(f17,plain,(
% 1.45/0.57    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.45/0.57    inference(cnf_transformation,[],[f12])).
% 1.45/0.57  fof(f12,plain,(
% 1.45/0.57    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.45/0.57    inference(ennf_transformation,[],[f11])).
% 1.45/0.57  fof(f11,negated_conjecture,(
% 1.45/0.57    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.45/0.57    inference(negated_conjecture,[],[f10])).
% 1.45/0.57  fof(f10,conjecture,(
% 1.45/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.45/0.57  fof(f67,plain,(
% 1.45/0.57    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f66,f19])).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    k1_xboole_0 != sK0),
% 1.45/0.57    inference(cnf_transformation,[],[f12])).
% 1.45/0.57  fof(f66,plain,(
% 1.45/0.57    k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f65,f21])).
% 1.45/0.57  fof(f21,plain,(
% 1.45/0.57    k1_xboole_0 != sK2),
% 1.45/0.57    inference(cnf_transformation,[],[f12])).
% 1.45/0.57  fof(f65,plain,(
% 1.45/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f62,f20])).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    k1_xboole_0 != sK1),
% 1.45/0.57    inference(cnf_transformation,[],[f12])).
% 1.45/0.57  fof(f62,plain,(
% 1.45/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 1.45/0.57    inference(resolution,[],[f44,f38])).
% 1.45/0.57  fof(f38,plain,(
% 1.45/0.57    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.45/0.57    inference(definition_unfolding,[],[f18,f29])).
% 1.45/0.57  fof(f29,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f5])).
% 1.45/0.57  fof(f5,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.45/0.57    inference(cnf_transformation,[],[f12])).
% 1.45/0.57  fof(f44,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.45/0.57    inference(definition_unfolding,[],[f37,f29])).
% 1.45/0.57  fof(f37,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.45/0.57    inference(ennf_transformation,[],[f9])).
% 1.45/0.57  fof(f9,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.45/0.57  fof(f79,plain,(
% 1.45/0.57    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f78,f19])).
% 1.45/0.57  fof(f78,plain,(
% 1.45/0.57    k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f77,f21])).
% 1.45/0.57  fof(f77,plain,(
% 1.45/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f74,f20])).
% 1.45/0.57  fof(f74,plain,(
% 1.45/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(resolution,[],[f45,f38])).
% 1.45/0.57  fof(f45,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 1.45/0.57    inference(definition_unfolding,[],[f36,f29])).
% 1.45/0.57  fof(f36,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f94,plain,(
% 1.45/0.57    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f93,f19])).
% 1.45/0.57  fof(f93,plain,(
% 1.45/0.57    k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f92,f21])).
% 1.45/0.57  fof(f92,plain,(
% 1.45/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f89,f20])).
% 1.45/0.57  fof(f89,plain,(
% 1.45/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 1.45/0.57    inference(resolution,[],[f46,f38])).
% 1.45/0.57  fof(f46,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.45/0.57    inference(definition_unfolding,[],[f35,f29])).
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f124,plain,(
% 1.45/0.57    ~r1_tarski(k1_tarski(k2_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3))),
% 1.45/0.57    inference(superposition,[],[f59,f115])).
% 1.45/0.57  fof(f115,plain,(
% 1.45/0.57    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))),
% 1.45/0.57    inference(forward_demodulation,[],[f114,f94])).
% 1.45/0.57  fof(f114,plain,(
% 1.45/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))),
% 1.45/0.57    inference(forward_demodulation,[],[f113,f79])).
% 1.45/0.57  fof(f113,plain,(
% 1.45/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3))),
% 1.45/0.57    inference(forward_demodulation,[],[f112,f67])).
% 1.45/0.57  fof(f112,plain,(
% 1.45/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f111,f19])).
% 1.45/0.57  fof(f111,plain,(
% 1.45/0.57    k1_xboole_0 = sK0 | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f110,f21])).
% 1.45/0.57  % (6864)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.57  fof(f110,plain,(
% 1.45/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f107,f20])).
% 1.45/0.57  fof(f107,plain,(
% 1.45/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.45/0.57    inference(resolution,[],[f43,f38])).
% 1.45/0.57  fof(f43,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) )),
% 1.45/0.57    inference(definition_unfolding,[],[f34,f29])).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.45/0.57    inference(ennf_transformation,[],[f7])).
% 1.45/0.57  fof(f7,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.45/0.57  fof(f59,plain,(
% 1.45/0.57    ( ! [X4,X5,X3] : (~r1_tarski(k1_tarski(X4),k1_tarski(k3_mcart_1(X3,X4,X5)))) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f53,f49])).
% 1.45/0.57  fof(f49,plain,(
% 1.45/0.57    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 1.45/0.57    inference(superposition,[],[f23,f22])).
% 1.45/0.57  fof(f22,plain,(
% 1.45/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.57    inference(cnf_transformation,[],[f1])).
% 1.45/0.57  fof(f1,axiom,(
% 1.45/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.45/0.57  fof(f23,plain,(
% 1.45/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.45/0.57  fof(f53,plain,(
% 1.45/0.57    ( ! [X4,X5,X3] : (~r1_tarski(k1_tarski(X4),k1_tarski(k3_mcart_1(X3,X4,X5))) | k1_xboole_0 = k1_tarski(X4)) )),
% 1.45/0.57    inference(superposition,[],[f40,f39])).
% 1.45/0.57  fof(f39,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k1_tarski(k3_mcart_1(X0,X1,X2)) = k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 1.45/0.57    inference(definition_unfolding,[],[f30,f29])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).
% 1.45/0.57  fof(f40,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(X2,X0),X1)) | k1_xboole_0 = X0) )),
% 1.45/0.57    inference(definition_unfolding,[],[f33,f29])).
% 1.45/0.57  fof(f33,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) | k1_xboole_0 = X0) )),
% 1.45/0.57    inference(cnf_transformation,[],[f14])).
% 1.45/0.57  fof(f14,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 1.45/0.57    inference(ennf_transformation,[],[f8])).
% 1.45/0.57  fof(f8,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).
% 1.45/0.57  fof(f123,plain,(
% 1.45/0.57    ~r1_tarski(k1_tarski(k1_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3))),
% 1.45/0.57    inference(superposition,[],[f58,f115])).
% 1.45/0.57  fof(f58,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(k3_mcart_1(X0,X1,X2)))) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f52,f49])).
% 1.45/0.57  fof(f52,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(k3_mcart_1(X0,X1,X2))) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.45/0.57    inference(superposition,[],[f42,f39])).
% 1.45/0.57  fof(f42,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.45/0.57    inference(definition_unfolding,[],[f31,f29])).
% 1.45/0.57  % (6864)Refutation not found, incomplete strategy% (6864)------------------------------
% 1.45/0.57  % (6864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  fof(f31,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f14])).
% 1.45/0.58  fof(f126,plain,(
% 1.45/0.58    ~r1_tarski(k1_tarski(k2_mcart_1(sK3)),k1_tarski(sK3))),
% 1.45/0.58    inference(superposition,[],[f61,f115])).
% 1.45/0.58  fof(f61,plain,(
% 1.45/0.58    ( ! [X14,X15,X16] : (~r1_tarski(k1_tarski(X16),k1_tarski(k3_mcart_1(X14,X15,X16)))) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f56,f49])).
% 1.45/0.58  fof(f56,plain,(
% 1.45/0.58    ( ! [X14,X15,X16] : (~r1_tarski(k1_tarski(X16),k1_tarski(k3_mcart_1(X14,X15,X16))) | k1_xboole_0 = k1_tarski(X16)) )),
% 1.45/0.58    inference(superposition,[],[f25,f39])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f13,plain,(
% 1.45/0.58    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.45/0.58    inference(ennf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (6861)------------------------------
% 1.45/0.58  % (6861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (6861)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (6861)Memory used [KB]: 6268
% 1.45/0.58  % (6861)Time elapsed: 0.147 s
% 1.45/0.58  % (6861)------------------------------
% 1.45/0.58  % (6861)------------------------------
% 1.45/0.58  % (6860)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.58  % (6877)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.58  % (6854)Success in time 0.221 s
%------------------------------------------------------------------------------
