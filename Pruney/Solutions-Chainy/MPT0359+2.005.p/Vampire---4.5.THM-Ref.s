%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 316 expanded)
%              Number of leaves         :   23 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          :  224 ( 546 expanded)
%              Number of equality atoms :   80 ( 272 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f70,f105,f244,f246,f350])).

fof(f350,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f348])).

fof(f348,plain,
    ( sK0 != sK0
    | ~ spl2_1
    | spl2_2
    | ~ spl2_10 ),
    inference(superposition,[],[f106,f281])).

fof(f281,plain,
    ( sK0 = sK1
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f141,f280])).

fof(f280,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f279,f86])).

fof(f86,plain,(
    ! [X4] : k3_tarski(k1_enumset1(X4,X4,k1_xboole_0)) = X4 ),
    inference(superposition,[],[f58,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f75,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

% (1992)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (1993)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

% (1990)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

% (1987)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f279,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f251,f178])).

fof(f178,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f122,f176])).

fof(f176,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f166,f46])).

fof(f166,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f163,f55])).

fof(f55,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f163,plain,(
    ! [X0] : r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) ),
    inference(resolution,[],[f161,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(k3_subset_1(X1,X0),X1) ) ),
    inference(resolution,[],[f149,f36])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,X1),X0) ) ),
    inference(forward_demodulation,[],[f147,f55])).

fof(f147,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f122,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f118,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f100,f36])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k1_xboole_0 = k3_subset_1(X0,X0) ) ),
    inference(superposition,[],[f48,f55])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

% (1983)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f118,plain,(
    ! [X1] : k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(resolution,[],[f60,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f56,f55])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f251,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k5_xboole_0(sK1,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f59,f248])).

fof(f248,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_10 ),
    inference(resolution,[],[f243,f46])).

fof(f243,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl2_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f45,f51,f44,f51])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

% (1984)Refutation not found, incomplete strategy% (1984)------------------------------
% (1984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1984)Termination reason: Refutation not found, incomplete strategy

% (1984)Memory used [KB]: 10746
% (1984)Time elapsed: 0.124 s
% (1984)------------------------------
% (1984)------------------------------
fof(f141,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f140,f110])).

fof(f110,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))
    | ~ spl2_1 ),
    inference(superposition,[],[f84,f107])).

fof(f107,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[],[f58,f40])).

fof(f140,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f131,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f43,f43])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f131,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(superposition,[],[f59,f119])).

fof(f119,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

% (1978)Refutation not found, incomplete strategy% (1978)------------------------------
% (1978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1978)Termination reason: Refutation not found, incomplete strategy

% (1978)Memory used [KB]: 10746
% (1978)Time elapsed: 0.110 s
% (1978)------------------------------
% (1978)------------------------------
fof(f25,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f106,plain,
    ( sK0 != sK1
    | spl2_2 ),
    inference(forward_demodulation,[],[f68,f55])).

fof(f68,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_2
  <=> sK1 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f246,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f239,f33])).

fof(f239,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl2_9
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f244,plain,
    ( ~ spl2_9
    | spl2_10 ),
    inference(avatar_split_clause,[],[f235,f241,f237])).

fof(f235,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f172,f30])).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | r1_tarski(X3,X2)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f169,f101])).

fof(f169,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_subset_1(X2,X2),k3_subset_1(X2,X3))
      | r1_tarski(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f50,f71])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f103,f33])).

fof(f103,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f74,f101])).

fof(f74,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f64,f72])).

fof(f72,plain,
    ( sK0 = sK1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f67,f55])).

fof(f67,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f64,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f70,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f54,f66,f62])).

fof(f54,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f31,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f53,f66,f62])).

fof(f53,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f32,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (1996)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (1985)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (1984)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (1985)Refutation not found, incomplete strategy% (1985)------------------------------
% 0.22/0.51  % (1985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1985)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1985)Memory used [KB]: 10746
% 0.22/0.51  % (1985)Time elapsed: 0.098 s
% 0.22/0.51  % (1985)------------------------------
% 0.22/0.51  % (1985)------------------------------
% 0.22/0.51  % (1988)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (1996)Refutation not found, incomplete strategy% (1996)------------------------------
% 0.22/0.52  % (1996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1980)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (1981)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (1980)Refutation not found, incomplete strategy% (1980)------------------------------
% 0.22/0.52  % (1980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1980)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1980)Memory used [KB]: 6268
% 0.22/0.52  % (1980)Time elapsed: 0.108 s
% 0.22/0.52  % (1980)------------------------------
% 0.22/0.52  % (1980)------------------------------
% 0.22/0.52  % (1978)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (1999)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (1986)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (1977)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (1996)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1996)Memory used [KB]: 10746
% 0.22/0.52  % (1996)Time elapsed: 0.097 s
% 0.22/0.52  % (1996)------------------------------
% 0.22/0.52  % (1996)------------------------------
% 0.22/0.53  % (1982)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (2004)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (1976)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (1998)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (1995)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (1998)Refutation not found, incomplete strategy% (1998)------------------------------
% 0.22/0.53  % (1998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1998)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (1998)Memory used [KB]: 10618
% 0.22/0.53  % (1998)Time elapsed: 0.083 s
% 0.22/0.53  % (1998)------------------------------
% 0.22/0.53  % (1998)------------------------------
% 0.22/0.53  % (1994)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (1988)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f69,f70,f105,f244,f246,f350])).
% 0.22/0.53  fof(f350,plain,(
% 0.22/0.53    ~spl2_1 | spl2_2 | ~spl2_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f349])).
% 0.22/0.53  fof(f349,plain,(
% 0.22/0.53    $false | (~spl2_1 | spl2_2 | ~spl2_10)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f348])).
% 0.22/0.53  fof(f348,plain,(
% 0.22/0.53    sK0 != sK0 | (~spl2_1 | spl2_2 | ~spl2_10)),
% 0.22/0.53    inference(superposition,[],[f106,f281])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    sK0 = sK1 | (~spl2_1 | ~spl2_10)),
% 0.22/0.53    inference(backward_demodulation,[],[f141,f280])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl2_10),
% 0.22/0.53    inference(forward_demodulation,[],[f279,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X4] : (k3_tarski(k1_enumset1(X4,X4,k1_xboole_0)) = X4) )),
% 0.22/0.53    inference(superposition,[],[f58,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f75,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f46,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  % (1992)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (1993)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.53  % (1990)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f41,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f42,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  % (1987)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0)) | ~spl2_10),
% 0.22/0.53    inference(forward_demodulation,[],[f251,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f122,f176])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 0.22/0.53    inference(resolution,[],[f166,f46])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f163,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f35,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f38,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k3_subset_1(X0,k1_xboole_0),X0)) )),
% 0.22/0.54    inference(resolution,[],[f161,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k3_subset_1(X1,X0),X1)) )),
% 0.22/0.54    inference(resolution,[],[f149,f36])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,X1),X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f147,f55])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(resolution,[],[f49,f33])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f118,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f100,f36])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.22/0.54    inference(superposition,[],[f48,f55])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.54  % (1983)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_subset_1(X1,X1)) )),
% 0.22/0.54    inference(resolution,[],[f60,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f56,f55])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f37,f52])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f47,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k5_xboole_0(sK1,sK1))) | ~spl2_10),
% 0.22/0.54    inference(superposition,[],[f59,f248])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_10),
% 0.22/0.54    inference(resolution,[],[f243,f46])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    r1_tarski(sK1,sK0) | ~spl2_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f241])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    spl2_10 <=> r1_tarski(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f45,f51,f44,f51])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.54  % (1984)Refutation not found, incomplete strategy% (1984)------------------------------
% 0.22/0.54  % (1984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1984)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1984)Memory used [KB]: 10746
% 0.22/0.54  % (1984)Time elapsed: 0.124 s
% 0.22/0.54  % (1984)------------------------------
% 0.22/0.54  % (1984)------------------------------
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl2_1),
% 0.22/0.54    inference(forward_demodulation,[],[f140,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) | ~spl2_1),
% 0.22/0.54    inference(superposition,[],[f84,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl2_1),
% 0.22/0.54    inference(resolution,[],[f63,f46])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    spl2_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0) )),
% 0.22/0.54    inference(superposition,[],[f58,f40])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.22/0.54    inference(forward_demodulation,[],[f131,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f39,f43,f43])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 0.22/0.54    inference(superposition,[],[f59,f119])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f60,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  % (1978)Refutation not found, incomplete strategy% (1978)------------------------------
% 0.22/0.54  % (1978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1978)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1978)Memory used [KB]: 10746
% 0.22/0.54  % (1978)Time elapsed: 0.110 s
% 0.22/0.54  % (1978)------------------------------
% 0.22/0.54  % (1978)------------------------------
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f18])).
% 0.22/0.54  fof(f18,conjecture,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    sK0 != sK1 | spl2_2),
% 0.22/0.54    inference(forward_demodulation,[],[f68,f55])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    sK1 != k3_subset_1(sK0,k1_xboole_0) | spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    spl2_2 <=> sK1 = k3_subset_1(sK0,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.54  fof(f246,plain,(
% 0.22/0.54    spl2_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f245])).
% 0.22/0.54  fof(f245,plain,(
% 0.22/0.54    $false | spl2_9),
% 0.22/0.54    inference(resolution,[],[f239,f33])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) | spl2_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f237])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    spl2_9 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    ~spl2_9 | spl2_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f235,f241,f237])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    r1_tarski(sK1,sK0) | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f172,f30])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | r1_tarski(X3,X2) | ~r1_tarski(k1_xboole_0,k3_subset_1(X2,X3))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f169,f101])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_tarski(k3_subset_1(X2,X2),k3_subset_1(X2,X3)) | r1_tarski(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.22/0.54    inference(resolution,[],[f50,f71])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    spl2_1 | ~spl2_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    $false | (spl2_1 | ~spl2_2)),
% 0.22/0.54    inference(resolution,[],[f103,f33])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,sK0) | (spl2_1 | ~spl2_2)),
% 0.22/0.54    inference(backward_demodulation,[],[f74,f101])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl2_1 | ~spl2_2)),
% 0.22/0.54    inference(forward_demodulation,[],[f64,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    sK0 = sK1 | ~spl2_2),
% 0.22/0.54    inference(forward_demodulation,[],[f67,f55])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f62])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    spl2_1 | spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f54,f66,f62])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f52])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ~spl2_1 | ~spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f53,f66,f62])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f32,f52])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (1988)------------------------------
% 0.22/0.54  % (1988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1988)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (1988)Memory used [KB]: 6396
% 0.22/0.54  % (1988)Time elapsed: 0.119 s
% 0.22/0.54  % (1988)------------------------------
% 0.22/0.54  % (1988)------------------------------
% 0.22/0.54  % (1986)Refutation not found, incomplete strategy% (1986)------------------------------
% 0.22/0.54  % (1986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1986)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1986)Memory used [KB]: 10618
% 0.22/0.54  % (1986)Time elapsed: 0.125 s
% 0.22/0.54  % (1986)------------------------------
% 0.22/0.54  % (1986)------------------------------
% 0.22/0.54  % (2003)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (2000)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (2005)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (2002)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (1979)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (1975)Success in time 0.177 s
%------------------------------------------------------------------------------
