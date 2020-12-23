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
% DateTime   : Thu Dec  3 12:47:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 714 expanded)
%              Number of leaves         :   25 ( 225 expanded)
%              Depth                    :   19
%              Number of atoms          :  379 (1487 expanded)
%              Number of equality atoms :   79 ( 400 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f703,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f85,f117,f143,f410,f414,f630,f633,f696,f702])).

fof(f702,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f142,f562])).

fof(f562,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f548,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl2_1 ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f77,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_1
  <=> v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f548,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f415,f546])).

fof(f546,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(resolution,[],[f545,f40])).

fof(f545,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f544,f468])).

fof(f468,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f404,f467])).

fof(f467,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f450,f358])).

fof(f358,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f351,f86])).

fof(f351,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0))
    | ~ spl2_4 ),
    inference(resolution,[],[f254,f57])).

fof(f57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f32])).

fof(f32,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f39,f52])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f254,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | k4_relat_1(k5_relat_1(X3,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X3)) )
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f250,f61])).

fof(f61,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f42,f34])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

% (25145)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f250,plain,
    ( ! [X3] :
        ( k4_relat_1(k5_relat_1(X3,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X3))
        | ~ v1_relat_1(X3) )
    | ~ spl2_4 ),
    inference(resolution,[],[f46,f108])).

fof(f108,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_4
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f450,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl2_8 ),
    inference(resolution,[],[f404,f42])).

fof(f404,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl2_8
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f544,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f543,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f56])).

fof(f543,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl2_9 ),
    inference(superposition,[],[f47,f431])).

fof(f431,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f416,f175])).

fof(f175,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f169,f34])).

fof(f169,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f167,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f167,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f165,f57])).

fof(f165,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f37])).

fof(f37,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f416,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl2_9 ),
    inference(resolution,[],[f409,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f409,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl2_9
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f415,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl2_9 ),
    inference(resolution,[],[f409,f42])).

fof(f142,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl2_7
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f696,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_6
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_6
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f694,f138])).

fof(f138,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_6
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

% (25152)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f694,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f693,f86])).

fof(f693,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f692,f648])).

fof(f648,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f260,f647])).

fof(f647,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f636,f86])).

fof(f636,plain,
    ( k4_relat_1(k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f277,f634])).

fof(f634,plain,
    ( k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl2_12 ),
    inference(resolution,[],[f625,f40])).

fof(f625,plain,
    ( v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl2_12
  <=> v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f277,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k4_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f276,f42])).

fof(f276,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f275,f108])).

fof(f275,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f268,f57])).

fof(f268,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_1 ),
    inference(superposition,[],[f48,f260])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f260,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f255,f86])).

fof(f255,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f252,f57])).

fof(f252,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k4_relat_1(k5_relat_1(X7,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X7)) ) ),
    inference(resolution,[],[f46,f34])).

fof(f692,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f686,f61])).

fof(f686,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f253,f108])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X0)) )
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f248,f86])).

fof(f248,plain,(
    ! [X0] :
      ( k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f46,f57])).

fof(f633,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_13 ),
    inference(subsumption_resolution,[],[f631,f276])).

fof(f631,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | spl2_13 ),
    inference(resolution,[],[f629,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f629,plain,
    ( ~ v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl2_13
  <=> v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f630,plain,
    ( spl2_12
    | ~ spl2_13
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f303,f107,f75,f627,f623])).

fof(f303,plain,
    ( ~ v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f302,f58])).

fof(f302,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f47,f292])).

fof(f292,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f278,f262])).

fof(f262,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f173,f260])).

fof(f173,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl2_4 ),
    inference(resolution,[],[f169,f108])).

fof(f278,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f276,f43])).

fof(f414,plain,
    ( ~ spl2_4
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f412,f57])).

fof(f412,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f411,f108])).

fof(f411,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl2_8 ),
    inference(resolution,[],[f405,f48])).

% (25146)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f405,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f403])).

fof(f410,plain,
    ( ~ spl2_8
    | spl2_9
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f376,f107,f75,f407,f403])).

fof(f376,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f41,f358])).

fof(f143,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f35,f140,f136])).

fof(f35,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f117,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f115,f34])).

fof(f115,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(resolution,[],[f109,f41])).

fof(f109,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f85,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f83,f57])).

fof(f83,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_2 ),
    inference(resolution,[],[f81,f41])).

fof(f81,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_2
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f82,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f72,f79,f75])).

fof(f72,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f71,f58])).

fof(f71,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f47,f70])).

fof(f70,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f68,f37])).

fof(f68,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f43,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (25159)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.49  % (25158)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.49  % (25137)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (25135)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (25161)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.50  % (25143)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (25153)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (25138)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (25150)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (25155)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (25161)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  % (25139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  fof(f703,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f82,f85,f117,f143,f410,f414,f630,f633,f696,f702])).
% 0.22/0.52  fof(f702,plain,(
% 0.22/0.52    ~spl2_1 | ~spl2_4 | spl2_7 | ~spl2_8 | ~spl2_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f701])).
% 0.22/0.52  fof(f701,plain,(
% 0.22/0.52    $false | (~spl2_1 | ~spl2_4 | spl2_7 | ~spl2_8 | ~spl2_9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f142,f562])).
% 0.22/0.52  fof(f562,plain,(
% 0.22/0.52    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f548,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl2_1),
% 0.22/0.52    inference(resolution,[],[f77,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl2_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl2_1 <=> v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.52  fof(f548,plain,(
% 0.22/0.52    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_9)),
% 0.22/0.52    inference(backward_demodulation,[],[f415,f546])).
% 0.22/0.52  fof(f546,plain,(
% 0.22/0.52    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_9)),
% 0.22/0.52    inference(resolution,[],[f545,f40])).
% 0.22/0.52  fof(f545,plain,(
% 0.22/0.52    v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f544,f468])).
% 0.22/0.52  fof(f468,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl2_1 | ~spl2_4 | ~spl2_8)),
% 0.22/0.52    inference(backward_demodulation,[],[f404,f467])).
% 0.22/0.52  fof(f467,plain,(
% 0.22/0.52    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl2_1 | ~spl2_4 | ~spl2_8)),
% 0.22/0.52    inference(forward_demodulation,[],[f450,f358])).
% 0.22/0.52  fof(f358,plain,(
% 0.22/0.52    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f351,f86])).
% 0.22/0.52  fof(f351,plain,(
% 0.22/0.52    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) | ~spl2_4),
% 0.22/0.52    inference(resolution,[],[f254,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f55,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(resolution,[],[f40,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    v1_xboole_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v1_xboole_0(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f39,f52])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    ( ! [X3] : (~v1_relat_1(X3) | k4_relat_1(k5_relat_1(X3,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X3))) ) | ~spl2_4),
% 0.22/0.52    inference(forward_demodulation,[],[f250,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    inference(resolution,[],[f42,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f14])).
% 0.22/0.52  fof(f14,conjecture,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  % (25145)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    ( ! [X3] : (k4_relat_1(k5_relat_1(X3,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X3)) | ~v1_relat_1(X3)) ) | ~spl2_4),
% 0.22/0.52    inference(resolution,[],[f46,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(sK0)) | ~spl2_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl2_4 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.52  fof(f450,plain,(
% 0.22/0.52    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | ~spl2_8),
% 0.22/0.52    inference(resolution,[],[f404,f42])).
% 0.22/0.52  fof(f404,plain,(
% 0.22/0.52    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl2_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f403])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    spl2_8 <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.52  fof(f544,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl2_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f543,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f52,f56])).
% 0.22/0.52  fof(f543,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl2_9),
% 0.22/0.52    inference(superposition,[],[f47,f431])).
% 0.22/0.52  fof(f431,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl2_9),
% 0.22/0.52    inference(forward_demodulation,[],[f416,f175])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.52    inference(resolution,[],[f169,f34])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 0.22/0.52    inference(resolution,[],[f167,f123])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(resolution,[],[f51,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f165,f57])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(superposition,[],[f45,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.52  fof(f416,plain,(
% 0.22/0.52    k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl2_9),
% 0.22/0.52    inference(resolution,[],[f409,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.52  fof(f409,plain,(
% 0.22/0.52    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl2_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f407])).
% 0.22/0.52  fof(f407,plain,(
% 0.22/0.52    spl2_9 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.52  fof(f415,plain,(
% 0.22/0.52    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl2_9),
% 0.22/0.52    inference(resolution,[],[f409,f42])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl2_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f140])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl2_7 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.52  fof(f696,plain,(
% 0.22/0.52    ~spl2_1 | ~spl2_4 | spl2_6 | ~spl2_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f695])).
% 0.22/0.52  fof(f695,plain,(
% 0.22/0.52    $false | (~spl2_1 | ~spl2_4 | spl2_6 | ~spl2_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f694,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl2_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f136])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    spl2_6 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.52  % (25152)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  fof(f694,plain,(
% 0.22/0.52    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_4 | ~spl2_12)),
% 0.22/0.52    inference(forward_demodulation,[],[f693,f86])).
% 0.22/0.52  fof(f693,plain,(
% 0.22/0.52    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) | (~spl2_1 | ~spl2_4 | ~spl2_12)),
% 0.22/0.52    inference(forward_demodulation,[],[f692,f648])).
% 0.22/0.52  fof(f648,plain,(
% 0.22/0.52    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) | (~spl2_1 | ~spl2_4 | ~spl2_12)),
% 0.22/0.52    inference(backward_demodulation,[],[f260,f647])).
% 0.22/0.52  fof(f647,plain,(
% 0.22/0.52    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_12)),
% 0.22/0.52    inference(forward_demodulation,[],[f636,f86])).
% 0.22/0.52  fof(f636,plain,(
% 0.22/0.52    k4_relat_1(k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_12)),
% 0.22/0.52    inference(backward_demodulation,[],[f277,f634])).
% 0.22/0.52  fof(f634,plain,(
% 0.22/0.52    k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl2_12),
% 0.22/0.52    inference(resolution,[],[f625,f40])).
% 0.22/0.52  fof(f625,plain,(
% 0.22/0.52    v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | ~spl2_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f623])).
% 0.22/0.52  fof(f623,plain,(
% 0.22/0.52    spl2_12 <=> v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k4_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(resolution,[],[f276,f42])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f275,f108])).
% 0.22/0.52  fof(f275,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~spl2_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f268,f57])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0)) | ~spl2_1),
% 0.22/0.52    inference(superposition,[],[f48,f260])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl2_1),
% 0.22/0.52    inference(forward_demodulation,[],[f255,f86])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))),
% 0.22/0.52    inference(resolution,[],[f252,f57])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(X7,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X7))) )),
% 0.22/0.52    inference(resolution,[],[f46,f34])).
% 0.22/0.52  fof(f692,plain,(
% 0.22/0.52    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f686,f61])).
% 0.22/0.52  fof(f686,plain,(
% 0.22/0.52    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(resolution,[],[f253,f108])).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X0))) ) | ~spl2_1),
% 0.22/0.52    inference(forward_demodulation,[],[f248,f86])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    ( ! [X0] : (k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f46,f57])).
% 0.22/0.52  fof(f633,plain,(
% 0.22/0.52    ~spl2_1 | ~spl2_4 | spl2_13),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f632])).
% 0.22/0.52  fof(f632,plain,(
% 0.22/0.52    $false | (~spl2_1 | ~spl2_4 | spl2_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f631,f276])).
% 0.22/0.52  fof(f631,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | spl2_13),
% 0.22/0.52    inference(resolution,[],[f629,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.52  fof(f629,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | spl2_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f627])).
% 0.22/0.52  fof(f627,plain,(
% 0.22/0.52    spl2_13 <=> v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.52  fof(f630,plain,(
% 0.22/0.52    spl2_12 | ~spl2_13 | ~spl2_1 | ~spl2_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f303,f107,f75,f627,f623])).
% 0.22/0.52  fof(f303,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f302,f58])).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(superposition,[],[f47,f292])).
% 0.22/0.52  fof(f292,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f278,f262])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(backward_demodulation,[],[f173,f260])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl2_4),
% 0.22/0.52    inference(resolution,[],[f169,f108])).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(resolution,[],[f276,f43])).
% 0.22/0.52  fof(f414,plain,(
% 0.22/0.52    ~spl2_4 | spl2_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f413])).
% 0.22/0.52  fof(f413,plain,(
% 0.22/0.52    $false | (~spl2_4 | spl2_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f412,f57])).
% 0.22/0.52  fof(f412,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | (~spl2_4 | spl2_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f411,f108])).
% 0.22/0.52  fof(f411,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl2_8),
% 0.22/0.52    inference(resolution,[],[f405,f48])).
% 0.22/0.52  % (25146)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  fof(f405,plain,(
% 0.22/0.52    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | spl2_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f403])).
% 0.22/0.52  fof(f410,plain,(
% 0.22/0.52    ~spl2_8 | spl2_9 | ~spl2_1 | ~spl2_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f376,f107,f75,f407,f403])).
% 0.22/0.52  fof(f376,plain,(
% 0.22/0.52    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.52    inference(superposition,[],[f41,f358])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ~spl2_6 | ~spl2_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f35,f140,f136])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl2_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f116])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    $false | spl2_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f115,f34])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | spl2_4),
% 0.22/0.52    inference(resolution,[],[f109,f41])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(sK0)) | spl2_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl2_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    $false | spl2_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f57])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | spl2_2),
% 0.22/0.52    inference(resolution,[],[f81,f41])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl2_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl2_2 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl2_1 | ~spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f72,f79,f75])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f71,f58])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.22/0.52    inference(superposition,[],[f47,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.52    inference(forward_demodulation,[],[f68,f37])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.52    inference(resolution,[],[f43,f57])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (25161)------------------------------
% 0.22/0.52  % (25161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25161)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (25161)Memory used [KB]: 11001
% 0.22/0.52  % (25161)Time elapsed: 0.066 s
% 0.22/0.52  % (25161)------------------------------
% 0.22/0.52  % (25161)------------------------------
% 0.22/0.52  % (25136)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (25147)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (25140)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (25131)Success in time 0.164 s
%------------------------------------------------------------------------------
