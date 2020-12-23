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
% DateTime   : Thu Dec  3 12:37:57 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 765 expanded)
%              Number of leaves         :   18 ( 221 expanded)
%              Depth                    :   17
%              Number of atoms          :  169 (2407 expanded)
%              Number of equality atoms :   90 (1677 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2004,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2003,f1954])).

fof(f1954,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f1779,f1869])).

fof(f1869,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1776,f1779])).

fof(f1776,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1771,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1771,plain,
    ( v1_xboole_0(sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f1769,f104])).

fof(f104,plain,(
    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f68,f83])).

fof(f83,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f57,f48])).

fof(f48,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1769,plain,
    ( v1_xboole_0(sK1)
    | k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f1766,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f1766,plain,
    ( r2_hidden(sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f1750,f104])).

fof(f1750,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1)))
      | r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f1739,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1739,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(k1_tarski(X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f95,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_tarski(X1),X2))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f64,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1779,plain,(
    sK1 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f51,f1778])).

fof(f1778,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f50,f49,f1776,f1777])).

fof(f1777,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1775,f55])).

fof(f1775,plain,
    ( v1_xboole_0(sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f1773,f405])).

fof(f405,plain,(
    sK2 = k3_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f355,f68])).

fof(f355,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f228,f338])).

fof(f338,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f333,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f333,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f62,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f228,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(sK2,X7),k1_tarski(sK0)) ),
    inference(superposition,[],[f165,f48])).

fof(f165,plain,(
    ! [X6,X7,X5] : r1_tarski(k4_xboole_0(X5,X6),k2_xboole_0(X7,X5)) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1773,plain,
    ( v1_xboole_0(sK2)
    | k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f1767,f66])).

fof(f1767,plain,
    ( r2_hidden(sK0,sK2)
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f1750,f405])).

fof(f49,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f2003,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f2002,f347])).

fof(f347,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = X3 ),
    inference(superposition,[],[f98,f338])).

fof(f98,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(resolution,[],[f67,f58])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2002,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1780,f1869])).

fof(f1780,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f48,f1778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (3878)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3873)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (3867)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (3874)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (3870)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (3891)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (3881)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3869)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (3871)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (3876)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (3881)Refutation not found, incomplete strategy% (3881)------------------------------
% 0.21/0.54  % (3881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3881)Memory used [KB]: 6140
% 0.21/0.54  % (3881)Time elapsed: 0.003 s
% 0.21/0.54  % (3881)------------------------------
% 0.21/0.54  % (3881)------------------------------
% 0.21/0.54  % (3887)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (3879)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (3894)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (3868)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3886)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (3893)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (3875)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (3872)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (3892)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (3883)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (3885)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (3883)Refutation not found, incomplete strategy% (3883)------------------------------
% 0.21/0.55  % (3883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3883)Memory used [KB]: 10618
% 0.21/0.55  % (3883)Time elapsed: 0.141 s
% 0.21/0.55  % (3883)------------------------------
% 0.21/0.55  % (3883)------------------------------
% 1.44/0.55  % (3895)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (3884)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.56  % (3890)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.56  % (3877)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.56  % (3882)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.62/0.58  % (3866)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.62/0.59  % (3888)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.62/0.59  % (3888)Refutation not found, incomplete strategy% (3888)------------------------------
% 1.62/0.59  % (3888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (3888)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (3888)Memory used [KB]: 10746
% 1.62/0.59  % (3888)Time elapsed: 0.174 s
% 1.62/0.59  % (3888)------------------------------
% 1.62/0.59  % (3888)------------------------------
% 1.62/0.59  % (3889)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.62/0.60  % (3873)Refutation found. Thanks to Tanya!
% 1.62/0.60  % SZS status Theorem for theBenchmark
% 1.62/0.60  % SZS output start Proof for theBenchmark
% 1.62/0.60  fof(f2004,plain,(
% 1.62/0.60    $false),
% 1.62/0.60    inference(subsumption_resolution,[],[f2003,f1954])).
% 1.62/0.60  fof(f1954,plain,(
% 1.62/0.60    k1_xboole_0 != k1_tarski(sK0)),
% 1.62/0.60    inference(backward_demodulation,[],[f1779,f1869])).
% 1.62/0.60  fof(f1869,plain,(
% 1.62/0.60    k1_xboole_0 = sK1),
% 1.62/0.60    inference(subsumption_resolution,[],[f1776,f1779])).
% 1.62/0.60  fof(f1776,plain,(
% 1.62/0.60    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.62/0.60    inference(resolution,[],[f1771,f55])).
% 1.62/0.60  fof(f55,plain,(
% 1.62/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f29])).
% 1.62/0.60  fof(f29,plain,(
% 1.62/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f3])).
% 1.62/0.60  fof(f3,axiom,(
% 1.62/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.62/0.60  fof(f1771,plain,(
% 1.62/0.60    v1_xboole_0(sK1) | sK1 = k1_tarski(sK0)),
% 1.62/0.60    inference(forward_demodulation,[],[f1769,f104])).
% 1.62/0.60  fof(f104,plain,(
% 1.62/0.60    sK1 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.62/0.60    inference(resolution,[],[f68,f83])).
% 1.62/0.60  fof(f83,plain,(
% 1.62/0.60    r1_tarski(sK1,k1_tarski(sK0))),
% 1.62/0.60    inference(superposition,[],[f57,f48])).
% 1.62/0.60  fof(f48,plain,(
% 1.62/0.60    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.62/0.60    inference(cnf_transformation,[],[f40])).
% 1.62/0.60  fof(f40,plain,(
% 1.62/0.60    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f39])).
% 1.62/0.60  fof(f39,plain,(
% 1.62/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f28,plain,(
% 1.62/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.62/0.60    inference(ennf_transformation,[],[f25])).
% 1.62/0.60  fof(f25,negated_conjecture,(
% 1.62/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.62/0.60    inference(negated_conjecture,[],[f24])).
% 1.62/0.60  fof(f24,conjecture,(
% 1.62/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.62/0.60  fof(f57,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f15])).
% 1.62/0.60  fof(f15,axiom,(
% 1.62/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.62/0.60  fof(f68,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f35])).
% 1.62/0.60  fof(f35,plain,(
% 1.62/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f11])).
% 1.62/0.60  fof(f11,axiom,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.62/0.60  fof(f1769,plain,(
% 1.62/0.60    v1_xboole_0(sK1) | k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.62/0.60    inference(resolution,[],[f1766,f66])).
% 1.62/0.60  fof(f66,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f33])).
% 1.62/0.60  fof(f33,plain,(
% 1.62/0.60    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f22])).
% 1.62/0.60  fof(f22,axiom,(
% 1.62/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.62/0.60  fof(f1766,plain,(
% 1.62/0.60    r2_hidden(sK0,sK1) | v1_xboole_0(sK1)),
% 1.62/0.60    inference(superposition,[],[f1750,f104])).
% 1.62/0.60  fof(f1750,plain,(
% 1.62/0.60    ( ! [X2,X1] : (v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1))) | r2_hidden(X1,X2)) )),
% 1.62/0.60    inference(superposition,[],[f1739,f59])).
% 1.62/0.60  fof(f59,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f1])).
% 1.62/0.60  fof(f1,axiom,(
% 1.62/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.62/0.60  fof(f1739,plain,(
% 1.62/0.60    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(k1_tarski(X0),X1)) | r2_hidden(X0,X1)) )),
% 1.62/0.60    inference(resolution,[],[f95,f56])).
% 1.62/0.60  fof(f56,plain,(
% 1.62/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f42])).
% 1.62/0.60  fof(f42,plain,(
% 1.62/0.60    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).
% 1.62/0.60  fof(f41,plain,(
% 1.62/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f30,plain,(
% 1.62/0.60    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f27])).
% 1.62/0.60  fof(f27,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.62/0.60    inference(unused_predicate_definition_removal,[],[f2])).
% 1.62/0.60  fof(f2,axiom,(
% 1.62/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.62/0.60  fof(f95,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_tarski(X1),X2)) | r2_hidden(X1,X2)) )),
% 1.62/0.60    inference(resolution,[],[f64,f65])).
% 1.62/0.60  fof(f65,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f32])).
% 1.62/0.60  fof(f32,plain,(
% 1.62/0.60    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f21])).
% 1.62/0.60  fof(f21,axiom,(
% 1.62/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.62/0.60  fof(f64,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f44])).
% 1.62/0.60  fof(f44,plain,(
% 1.62/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f43])).
% 1.62/0.60  fof(f43,plain,(
% 1.62/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f31,plain,(
% 1.62/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.62/0.60    inference(ennf_transformation,[],[f26])).
% 1.62/0.60  fof(f26,plain,(
% 1.62/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.62/0.60    inference(rectify,[],[f5])).
% 1.62/0.60  fof(f5,axiom,(
% 1.62/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.62/0.60  fof(f1779,plain,(
% 1.62/0.60    sK1 != k1_tarski(sK0)),
% 1.62/0.60    inference(subsumption_resolution,[],[f51,f1778])).
% 1.62/0.60  fof(f1778,plain,(
% 1.62/0.60    k1_xboole_0 = sK2),
% 1.62/0.60    inference(global_subsumption,[],[f50,f49,f1776,f1777])).
% 1.62/0.61  fof(f1777,plain,(
% 1.62/0.61    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK2),
% 1.62/0.61    inference(resolution,[],[f1775,f55])).
% 1.62/0.61  fof(f1775,plain,(
% 1.62/0.61    v1_xboole_0(sK2) | sK2 = k1_tarski(sK0)),
% 1.62/0.61    inference(forward_demodulation,[],[f1773,f405])).
% 1.62/0.61  fof(f405,plain,(
% 1.62/0.61    sK2 = k3_xboole_0(sK2,k1_tarski(sK0))),
% 1.62/0.61    inference(resolution,[],[f355,f68])).
% 1.62/0.61  fof(f355,plain,(
% 1.62/0.61    r1_tarski(sK2,k1_tarski(sK0))),
% 1.62/0.61    inference(superposition,[],[f228,f338])).
% 1.62/0.61  fof(f338,plain,(
% 1.62/0.61    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.62/0.61    inference(forward_demodulation,[],[f333,f53])).
% 1.62/0.61  fof(f53,plain,(
% 1.62/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.61    inference(cnf_transformation,[],[f14])).
% 1.62/0.61  fof(f14,axiom,(
% 1.62/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.62/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.62/0.61  fof(f333,plain,(
% 1.62/0.61    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 1.62/0.61    inference(superposition,[],[f62,f52])).
% 1.62/0.61  fof(f52,plain,(
% 1.62/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.62/0.61    inference(cnf_transformation,[],[f12])).
% 1.62/0.61  fof(f12,axiom,(
% 1.62/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.62/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.62/0.61  fof(f62,plain,(
% 1.62/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.61    inference(cnf_transformation,[],[f7])).
% 1.62/0.61  fof(f7,axiom,(
% 1.62/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.62/0.61  fof(f228,plain,(
% 1.62/0.61    ( ! [X7] : (r1_tarski(k4_xboole_0(sK2,X7),k1_tarski(sK0))) )),
% 1.62/0.61    inference(superposition,[],[f165,f48])).
% 1.62/0.61  fof(f165,plain,(
% 1.62/0.61    ( ! [X6,X7,X5] : (r1_tarski(k4_xboole_0(X5,X6),k2_xboole_0(X7,X5))) )),
% 1.62/0.61    inference(resolution,[],[f74,f58])).
% 1.62/0.61  fof(f58,plain,(
% 1.62/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.62/0.61    inference(cnf_transformation,[],[f13])).
% 1.62/0.61  fof(f13,axiom,(
% 1.62/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.62/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.62/0.61  fof(f74,plain,(
% 1.62/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.62/0.61    inference(cnf_transformation,[],[f36])).
% 1.62/0.61  fof(f36,plain,(
% 1.62/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.62/0.61    inference(ennf_transformation,[],[f8])).
% 1.62/0.61  fof(f8,axiom,(
% 1.62/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.62/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.62/0.61  fof(f1773,plain,(
% 1.62/0.61    v1_xboole_0(sK2) | k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0))),
% 1.62/0.61    inference(resolution,[],[f1767,f66])).
% 1.62/0.61  fof(f1767,plain,(
% 1.62/0.61    r2_hidden(sK0,sK2) | v1_xboole_0(sK2)),
% 1.62/0.61    inference(superposition,[],[f1750,f405])).
% 1.62/0.61  fof(f49,plain,(
% 1.62/0.61    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.62/0.61    inference(cnf_transformation,[],[f40])).
% 1.62/0.61  fof(f50,plain,(
% 1.62/0.61    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.62/0.61    inference(cnf_transformation,[],[f40])).
% 1.62/0.61  fof(f51,plain,(
% 1.62/0.61    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.62/0.61    inference(cnf_transformation,[],[f40])).
% 1.62/0.61  fof(f2003,plain,(
% 1.62/0.61    k1_xboole_0 = k1_tarski(sK0)),
% 1.62/0.61    inference(forward_demodulation,[],[f2002,f347])).
% 1.62/0.61  fof(f347,plain,(
% 1.62/0.61    ( ! [X3] : (k2_xboole_0(X3,X3) = X3) )),
% 1.62/0.61    inference(superposition,[],[f98,f338])).
% 1.62/0.61  fof(f98,plain,(
% 1.62/0.61    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 1.62/0.61    inference(resolution,[],[f67,f58])).
% 1.62/0.61  fof(f67,plain,(
% 1.62/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.62/0.61    inference(cnf_transformation,[],[f34])).
% 1.62/0.61  fof(f34,plain,(
% 1.62/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.62/0.61    inference(ennf_transformation,[],[f9])).
% 1.62/0.61  fof(f9,axiom,(
% 1.62/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.62/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.62/0.61  fof(f2002,plain,(
% 1.62/0.61    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.62/0.61    inference(forward_demodulation,[],[f1780,f1869])).
% 1.62/0.61  fof(f1780,plain,(
% 1.62/0.61    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.62/0.61    inference(backward_demodulation,[],[f48,f1778])).
% 1.62/0.61  % SZS output end Proof for theBenchmark
% 1.62/0.61  % (3873)------------------------------
% 1.62/0.61  % (3873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.61  % (3873)Termination reason: Refutation
% 1.62/0.61  
% 1.62/0.61  % (3873)Memory used [KB]: 7675
% 1.62/0.61  % (3873)Time elapsed: 0.185 s
% 1.62/0.61  % (3873)------------------------------
% 1.62/0.61  % (3873)------------------------------
% 1.62/0.61  % (3865)Success in time 0.245 s
%------------------------------------------------------------------------------
