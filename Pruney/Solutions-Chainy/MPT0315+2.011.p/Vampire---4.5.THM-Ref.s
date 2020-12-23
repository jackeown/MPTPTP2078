%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 170 expanded)
%              Number of leaves         :   12 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  140 ( 371 expanded)
%              Number of equality atoms :   48 ( 134 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f975,f1105])).

fof(f1105,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1104])).

fof(f1104,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1092,f46])).

fof(f46,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1092,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f534,f21])).

fof(f21,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    & ( r1_xboole_0(sK2,sK3)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
      & ( r1_xboole_0(sK2,sK3)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f534,plain,(
    ! [X30,X31,X29,X32] :
      ( r1_xboole_0(k2_zfmisc_1(X29,X30),k2_zfmisc_1(X31,X32))
      | ~ r1_xboole_0(X30,X32) ) ),
    inference(trivial_inequality_removal,[],[f518])).

fof(f518,plain,(
    ! [X30,X31,X29,X32] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(X29,X30),k2_zfmisc_1(X31,X32))
      | ~ r1_xboole_0(X30,X32) ) ),
    inference(superposition,[],[f103,f146])).

% (23688)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f146,plain,(
    ! [X6,X4,X5,X3] :
      ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f145,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

% (23691)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f145,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f136,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f49,f22])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f33,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f136,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X3,X3))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f36,f27])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f32,f24,f24,f24])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

% (23677)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f95,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f89,f22])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f28,f33])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X2,k4_xboole_0(X2,X3))
      | ~ r1_xboole_0(X2,X3)
      | ~ r2_hidden(X4,X2) ) ),
    inference(superposition,[],[f34,f27])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f24])).

% (23691)Refutation not found, incomplete strategy% (23691)------------------------------
% (23691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23691)Termination reason: Refutation not found, incomplete strategy

% (23691)Memory used [KB]: 10618
% (23691)Time elapsed: 0.130 s
% (23691)------------------------------
% (23691)------------------------------
fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f975,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f963,f40])).

fof(f40,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f963,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f416,f21])).

fof(f416,plain,(
    ! [X28,X26,X27,X25] :
      ( r1_xboole_0(k2_zfmisc_1(X25,X26),k2_zfmisc_1(X27,X28))
      | ~ r1_xboole_0(X25,X27) ) ),
    inference(trivial_inequality_removal,[],[f400])).

fof(f400,plain,(
    ! [X28,X26,X27,X25] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(X25,X26),k2_zfmisc_1(X27,X28))
      | ~ r1_xboole_0(X25,X27) ) ),
    inference(superposition,[],[f103,f142])).

fof(f142,plain,(
    ! [X6,X4,X5,X3] :
      ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f141,f38])).

fof(f38,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,X6)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f131,f51])).

fof(f131,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k4_xboole_0(X3,X3),k4_xboole_0(X5,k4_xboole_0(X5,X6)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f36,f27])).

fof(f47,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f20,f44,f40])).

fof(f20,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (23701)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.47  % (23692)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (23681)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (23675)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (23690)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (23676)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (23674)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (23686)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (23679)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (23674)Refutation not found, incomplete strategy% (23674)------------------------------
% 0.20/0.52  % (23674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23674)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23674)Memory used [KB]: 1663
% 0.20/0.52  % (23674)Time elapsed: 0.125 s
% 0.20/0.52  % (23674)------------------------------
% 0.20/0.52  % (23674)------------------------------
% 0.20/0.52  % (23678)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (23696)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (23684)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (23696)Refutation not found, incomplete strategy% (23696)------------------------------
% 0.20/0.53  % (23696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23696)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23696)Memory used [KB]: 10618
% 0.20/0.53  % (23696)Time elapsed: 0.089 s
% 0.20/0.53  % (23696)------------------------------
% 0.20/0.53  % (23696)------------------------------
% 0.20/0.53  % (23701)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (23684)Refutation not found, incomplete strategy% (23684)------------------------------
% 0.20/0.53  % (23684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23684)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23684)Memory used [KB]: 10618
% 0.20/0.53  % (23684)Time elapsed: 0.127 s
% 0.20/0.53  % (23684)------------------------------
% 0.20/0.53  % (23684)------------------------------
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1111,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f47,f975,f1105])).
% 0.20/0.53  fof(f1105,plain,(
% 0.20/0.53    ~spl5_2),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1104])).
% 0.20/0.53  fof(f1104,plain,(
% 0.20/0.53    $false | ~spl5_2),
% 0.20/0.53    inference(subsumption_resolution,[],[f1092,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    r1_xboole_0(sK2,sK3) | ~spl5_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    spl5_2 <=> r1_xboole_0(sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.53  fof(f1092,plain,(
% 0.20/0.53    ~r1_xboole_0(sK2,sK3)),
% 0.20/0.53    inference(resolution,[],[f534,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1))) => (~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.53  fof(f534,plain,(
% 0.20/0.53    ( ! [X30,X31,X29,X32] : (r1_xboole_0(k2_zfmisc_1(X29,X30),k2_zfmisc_1(X31,X32)) | ~r1_xboole_0(X30,X32)) )),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f518])).
% 0.20/0.53  fof(f518,plain,(
% 0.20/0.53    ( ! [X30,X31,X29,X32] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X29,X30),k2_zfmisc_1(X31,X32)) | ~r1_xboole_0(X30,X32)) )),
% 0.20/0.53    inference(superposition,[],[f103,f146])).
% 0.20/0.53  % (23688)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ( ! [X6,X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) | ~r1_xboole_0(X3,X4)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f145,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  % (23691)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) | ~r1_xboole_0(X3,X4)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f136,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f49,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(superposition,[],[f33,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f23,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X3,X3)) | ~r1_xboole_0(X3,X4)) )),
% 0.20/0.53    inference(superposition,[],[f36,f27])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f32,f24,f24,f24])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.20/0.53  % (23677)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f95,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f25,f24])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f89,f22])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,k1_xboole_0) | ~r2_hidden(X1,X0) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(resolution,[],[f70,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(superposition,[],[f28,f33])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X4,X2,X3] : (~r1_xboole_0(X2,k4_xboole_0(X2,X3)) | ~r1_xboole_0(X2,X3) | ~r2_hidden(X4,X2)) )),
% 0.20/0.53    inference(superposition,[],[f34,f27])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f26,f24])).
% 0.20/0.53  % (23691)Refutation not found, incomplete strategy% (23691)------------------------------
% 0.20/0.53  % (23691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23691)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23691)Memory used [KB]: 10618
% 0.20/0.53  % (23691)Time elapsed: 0.130 s
% 0.20/0.53  % (23691)------------------------------
% 0.20/0.53  % (23691)------------------------------
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f975,plain,(
% 0.20/0.53    ~spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f963,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.53  fof(f963,plain,(
% 0.20/0.53    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f416,f21])).
% 0.20/0.53  fof(f416,plain,(
% 0.20/0.53    ( ! [X28,X26,X27,X25] : (r1_xboole_0(k2_zfmisc_1(X25,X26),k2_zfmisc_1(X27,X28)) | ~r1_xboole_0(X25,X27)) )),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f400])).
% 0.20/0.53  fof(f400,plain,(
% 0.20/0.53    ( ! [X28,X26,X27,X25] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X25,X26),k2_zfmisc_1(X27,X28)) | ~r1_xboole_0(X25,X27)) )),
% 0.20/0.53    inference(superposition,[],[f103,f142])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ( ! [X6,X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) | ~r1_xboole_0(X3,X4)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f141,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,X6))) | ~r1_xboole_0(X3,X4)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f131,f51])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k4_xboole_0(X3,X3),k4_xboole_0(X5,k4_xboole_0(X5,X6))) | ~r1_xboole_0(X3,X4)) )),
% 0.20/0.53    inference(superposition,[],[f36,f27])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    spl5_1 | spl5_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f20,f44,f40])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (23701)------------------------------
% 0.20/0.53  % (23701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23701)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (23701)Memory used [KB]: 6780
% 0.20/0.53  % (23701)Time elapsed: 0.130 s
% 0.20/0.53  % (23701)------------------------------
% 0.20/0.53  % (23701)------------------------------
% 0.20/0.53  % (23683)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (23695)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (23673)Success in time 0.176 s
%------------------------------------------------------------------------------
