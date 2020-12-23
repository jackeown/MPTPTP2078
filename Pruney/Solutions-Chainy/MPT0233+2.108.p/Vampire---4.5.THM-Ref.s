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
% DateTime   : Thu Dec  3 12:37:18 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 214 expanded)
%              Number of leaves         :   11 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 ( 542 expanded)
%              Number of equality atoms :  105 ( 324 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f176,f266,f358,f402])).

fof(f402,plain,
    ( spl7_2
    | spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f400,f88])).

fof(f88,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f52,f52,f52])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f400,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(forward_demodulation,[],[f399,f56])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f399,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0))
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(resolution,[],[f385,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f385,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_xboole_0)
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(superposition,[],[f79,f361])).

fof(f361,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f360,f113])).

fof(f113,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_4
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f360,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | spl7_2
    | spl7_3 ),
    inference(subsumption_resolution,[],[f268,f109])).

fof(f109,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK3,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_3
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f268,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f178,f105])).

% (16820)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f105,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_2
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f178,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3)
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f32,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f52,f52])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f32,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f79,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X2,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f358,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f352,f317])).

fof(f317,plain,
    ( sK0 != sK1
    | ~ spl7_4 ),
    inference(superposition,[],[f33,f298])).

fof(f298,plain,
    ( sK1 = sK2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f297,f33])).

fof(f297,plain,
    ( sK1 = sK2
    | sK0 = sK2
    | ~ spl7_4 ),
    inference(resolution,[],[f279,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f279,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl7_4 ),
    inference(superposition,[],[f84,f114])).

fof(f114,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f84,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f352,plain,
    ( sK0 = sK1
    | ~ spl7_4 ),
    inference(resolution,[],[f314,f86])).

fof(f86,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f314,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tarski(sK0,sK1))
        | sK1 = X3 )
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f287,f298])).

fof(f287,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tarski(sK0,sK1))
        | sK2 = X3 )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tarski(sK0,sK1))
        | sK2 = X3
        | sK2 = X3 )
    | ~ spl7_4 ),
    inference(superposition,[],[f87,f114])).

fof(f266,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f260,f225])).

fof(f225,plain,
    ( sK0 != sK1
    | ~ spl7_3 ),
    inference(superposition,[],[f34,f206])).

fof(f206,plain,
    ( sK1 = sK3
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f205,f34])).

fof(f205,plain,
    ( sK1 = sK3
    | sK0 = sK3
    | ~ spl7_3 ),
    inference(resolution,[],[f187,f87])).

fof(f187,plain,
    ( r2_hidden(sK3,k2_tarski(sK0,sK1))
    | ~ spl7_3 ),
    inference(superposition,[],[f84,f110])).

fof(f110,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f34,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f260,plain,
    ( sK0 = sK1
    | ~ spl7_3 ),
    inference(resolution,[],[f222,f86])).

fof(f222,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tarski(sK0,sK1))
        | sK1 = X3 )
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f195,f206])).

fof(f195,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tarski(sK0,sK1))
        | sK3 = X3 )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tarski(sK0,sK1))
        | sK3 = X3
        | sK3 = X3 )
    | ~ spl7_3 ),
    inference(superposition,[],[f87,f110])).

fof(f176,plain,
    ( ~ spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f160,f164])).

fof(f164,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f140,f159])).

fof(f159,plain,
    ( sK1 = sK2
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f158,f33])).

fof(f158,plain,
    ( sK1 = sK2
    | sK0 = sK2
    | ~ spl7_2 ),
    inference(resolution,[],[f136,f87])).

fof(f136,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl7_2 ),
    inference(superposition,[],[f86,f106])).

fof(f106,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f140,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK1)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f106,f139])).

fof(f139,plain,
    ( sK1 = sK3
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,
    ( sK1 = sK3
    | sK0 = sK3
    | ~ spl7_2 ),
    inference(resolution,[],[f135,f87])).

fof(f135,plain,
    ( r2_hidden(sK3,k2_tarski(sK0,sK1))
    | ~ spl7_2 ),
    inference(superposition,[],[f84,f106])).

fof(f160,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK1,sK1)
    | ~ spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f113,f159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n019.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:53:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.10/0.52  % (16819)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.10/0.53  % (16811)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.10/0.53  % (16816)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.10/0.53  % (16803)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.10/0.53  % (16796)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.10/0.53  % (16793)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.10/0.53  % (16800)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.10/0.53  % (16794)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.10/0.53  % (16801)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.10/0.53  % (16805)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.10/0.53  % (16792)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.10/0.54  % (16808)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.10/0.54  % (16807)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.10/0.54  % (16819)Refutation found. Thanks to Tanya!
% 1.10/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (16814)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.54  % (16795)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (16815)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.54  % (16808)Refutation not found, incomplete strategy% (16808)------------------------------
% 1.32/0.54  % (16808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (16808)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (16808)Memory used [KB]: 10618
% 1.32/0.54  % (16808)Time elapsed: 0.116 s
% 1.32/0.54  % (16808)------------------------------
% 1.32/0.54  % (16808)------------------------------
% 1.32/0.54  % (16806)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.54  % (16813)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.54  % (16817)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.54  % (16804)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.55  % (16799)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.55  % (16812)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.55  % (16821)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.55  % (16809)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.55  % (16821)Refutation not found, incomplete strategy% (16821)------------------------------
% 1.32/0.55  % (16821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (16821)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (16821)Memory used [KB]: 1663
% 1.32/0.55  % (16821)Time elapsed: 0.130 s
% 1.32/0.55  % (16821)------------------------------
% 1.32/0.55  % (16821)------------------------------
% 1.32/0.55  % (16797)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.55  % (16802)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.56  % SZS output start Proof for theBenchmark
% 1.32/0.56  fof(f403,plain,(
% 1.32/0.56    $false),
% 1.32/0.56    inference(avatar_sat_refutation,[],[f176,f266,f358,f402])).
% 1.32/0.56  fof(f402,plain,(
% 1.32/0.56    spl7_2 | spl7_3 | spl7_4),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f401])).
% 1.32/0.56  fof(f401,plain,(
% 1.32/0.56    $false | (spl7_2 | spl7_3 | spl7_4)),
% 1.32/0.56    inference(subsumption_resolution,[],[f400,f88])).
% 1.32/0.56  fof(f88,plain,(
% 1.32/0.56    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 1.32/0.56    inference(equality_resolution,[],[f72])).
% 1.32/0.56  fof(f72,plain,(
% 1.32/0.56    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f54,f52,f52,f52])).
% 1.32/0.56  fof(f52,plain,(
% 1.32/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f12])).
% 1.32/0.56  fof(f12,axiom,(
% 1.32/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.56  fof(f54,plain,(
% 1.32/0.56    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f21])).
% 1.32/0.56  fof(f21,axiom,(
% 1.32/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.32/0.56  fof(f400,plain,(
% 1.32/0.56    k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) | (spl7_2 | spl7_3 | spl7_4)),
% 1.32/0.56    inference(forward_demodulation,[],[f399,f56])).
% 1.32/0.56  fof(f56,plain,(
% 1.32/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.56    inference(cnf_transformation,[],[f8])).
% 1.32/0.56  fof(f8,axiom,(
% 1.32/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.32/0.56  fof(f399,plain,(
% 1.32/0.56    k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0)) | (spl7_2 | spl7_3 | spl7_4)),
% 1.32/0.56    inference(resolution,[],[f385,f67])).
% 1.32/0.56  fof(f67,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.32/0.56    inference(definition_unfolding,[],[f41,f58])).
% 1.32/0.56  fof(f58,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f9])).
% 1.32/0.56  fof(f9,axiom,(
% 1.32/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.56  fof(f41,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.32/0.56    inference(cnf_transformation,[],[f29])).
% 1.32/0.56  fof(f29,plain,(
% 1.32/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.32/0.56    inference(ennf_transformation,[],[f7])).
% 1.32/0.56  fof(f7,axiom,(
% 1.32/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.32/0.56  fof(f385,plain,(
% 1.32/0.56    r1_tarski(k2_tarski(sK1,sK1),k1_xboole_0) | (spl7_2 | spl7_3 | spl7_4)),
% 1.32/0.56    inference(superposition,[],[f79,f361])).
% 1.32/0.56  fof(f361,plain,(
% 1.32/0.56    k1_xboole_0 = k2_tarski(sK0,sK1) | (spl7_2 | spl7_3 | spl7_4)),
% 1.32/0.56    inference(subsumption_resolution,[],[f360,f113])).
% 1.32/0.56  fof(f113,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2) | spl7_4),
% 1.32/0.56    inference(avatar_component_clause,[],[f112])).
% 1.32/0.56  fof(f112,plain,(
% 1.32/0.56    spl7_4 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.32/0.56  fof(f360,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | (spl7_2 | spl7_3)),
% 1.32/0.56    inference(subsumption_resolution,[],[f268,f109])).
% 1.32/0.56  fof(f109,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) != k2_tarski(sK3,sK3) | spl7_3),
% 1.32/0.56    inference(avatar_component_clause,[],[f108])).
% 1.32/0.56  fof(f108,plain,(
% 1.32/0.56    spl7_3 <=> k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.32/0.56  fof(f268,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3) | k1_xboole_0 = k2_tarski(sK0,sK1) | spl7_2),
% 1.32/0.56    inference(subsumption_resolution,[],[f178,f105])).
% 1.32/0.56  % (16820)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.56  fof(f105,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) != k2_tarski(sK2,sK3) | spl7_2),
% 1.32/0.56    inference(avatar_component_clause,[],[f104])).
% 1.32/0.56  fof(f104,plain,(
% 1.32/0.56    spl7_2 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.32/0.56  fof(f178,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.32/0.56    inference(resolution,[],[f32,f65])).
% 1.32/0.56  fof(f65,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.32/0.56    inference(definition_unfolding,[],[f35,f52,f52])).
% 1.32/0.56  fof(f35,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f27])).
% 1.32/0.56  fof(f27,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f20])).
% 1.32/0.56  fof(f20,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.32/0.56  fof(f32,plain,(
% 1.32/0.56    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.32/0.56    inference(cnf_transformation,[],[f26])).
% 1.32/0.56  fof(f26,plain,(
% 1.32/0.56    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.32/0.56    inference(ennf_transformation,[],[f23])).
% 1.32/0.56  fof(f23,negated_conjecture,(
% 1.32/0.56    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.32/0.56    inference(negated_conjecture,[],[f22])).
% 1.32/0.56  fof(f22,conjecture,(
% 1.32/0.56    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.32/0.56  fof(f79,plain,(
% 1.32/0.56    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 1.32/0.56    inference(equality_resolution,[],[f63])).
% 1.32/0.56  fof(f63,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_tarski(X2,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f38,f52])).
% 1.32/0.56  fof(f38,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f27])).
% 1.32/0.56  fof(f358,plain,(
% 1.32/0.56    ~spl7_4),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f357])).
% 1.32/0.56  fof(f357,plain,(
% 1.32/0.56    $false | ~spl7_4),
% 1.32/0.56    inference(subsumption_resolution,[],[f352,f317])).
% 1.32/0.56  fof(f317,plain,(
% 1.32/0.56    sK0 != sK1 | ~spl7_4),
% 1.32/0.56    inference(superposition,[],[f33,f298])).
% 1.32/0.56  fof(f298,plain,(
% 1.32/0.56    sK1 = sK2 | ~spl7_4),
% 1.32/0.56    inference(subsumption_resolution,[],[f297,f33])).
% 1.32/0.56  fof(f297,plain,(
% 1.32/0.56    sK1 = sK2 | sK0 = sK2 | ~spl7_4),
% 1.32/0.56    inference(resolution,[],[f279,f87])).
% 1.32/0.56  fof(f87,plain,(
% 1.32/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.32/0.56    inference(equality_resolution,[],[f49])).
% 1.32/0.56  fof(f49,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  fof(f11,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.32/0.56  fof(f279,plain,(
% 1.32/0.56    r2_hidden(sK2,k2_tarski(sK0,sK1)) | ~spl7_4),
% 1.32/0.56    inference(superposition,[],[f84,f114])).
% 1.32/0.56  fof(f114,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | ~spl7_4),
% 1.32/0.56    inference(avatar_component_clause,[],[f112])).
% 1.32/0.56  fof(f84,plain,(
% 1.32/0.56    ( ! [X0,X3] : (r2_hidden(X3,k2_tarski(X0,X3))) )),
% 1.32/0.56    inference(equality_resolution,[],[f83])).
% 1.32/0.56  fof(f83,plain,(
% 1.32/0.56    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_tarski(X0,X3) != X2) )),
% 1.32/0.56    inference(equality_resolution,[],[f51])).
% 1.32/0.56  fof(f51,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  fof(f33,plain,(
% 1.32/0.56    sK0 != sK2),
% 1.32/0.56    inference(cnf_transformation,[],[f26])).
% 1.32/0.56  fof(f352,plain,(
% 1.32/0.56    sK0 = sK1 | ~spl7_4),
% 1.32/0.56    inference(resolution,[],[f314,f86])).
% 1.32/0.56  fof(f86,plain,(
% 1.32/0.56    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 1.32/0.56    inference(equality_resolution,[],[f85])).
% 1.32/0.56  fof(f85,plain,(
% 1.32/0.56    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 1.32/0.56    inference(equality_resolution,[],[f50])).
% 1.32/0.56  fof(f50,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  fof(f314,plain,(
% 1.32/0.56    ( ! [X3] : (~r2_hidden(X3,k2_tarski(sK0,sK1)) | sK1 = X3) ) | ~spl7_4),
% 1.32/0.56    inference(backward_demodulation,[],[f287,f298])).
% 1.32/0.56  fof(f287,plain,(
% 1.32/0.56    ( ! [X3] : (~r2_hidden(X3,k2_tarski(sK0,sK1)) | sK2 = X3) ) | ~spl7_4),
% 1.32/0.56    inference(duplicate_literal_removal,[],[f281])).
% 1.32/0.56  fof(f281,plain,(
% 1.32/0.56    ( ! [X3] : (~r2_hidden(X3,k2_tarski(sK0,sK1)) | sK2 = X3 | sK2 = X3) ) | ~spl7_4),
% 1.32/0.56    inference(superposition,[],[f87,f114])).
% 1.32/0.56  fof(f266,plain,(
% 1.32/0.56    ~spl7_3),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f265])).
% 1.32/0.56  fof(f265,plain,(
% 1.32/0.56    $false | ~spl7_3),
% 1.32/0.56    inference(subsumption_resolution,[],[f260,f225])).
% 1.32/0.56  fof(f225,plain,(
% 1.32/0.56    sK0 != sK1 | ~spl7_3),
% 1.32/0.56    inference(superposition,[],[f34,f206])).
% 1.32/0.56  fof(f206,plain,(
% 1.32/0.56    sK1 = sK3 | ~spl7_3),
% 1.32/0.56    inference(subsumption_resolution,[],[f205,f34])).
% 1.32/0.56  fof(f205,plain,(
% 1.32/0.56    sK1 = sK3 | sK0 = sK3 | ~spl7_3),
% 1.32/0.56    inference(resolution,[],[f187,f87])).
% 1.32/0.56  fof(f187,plain,(
% 1.32/0.56    r2_hidden(sK3,k2_tarski(sK0,sK1)) | ~spl7_3),
% 1.32/0.56    inference(superposition,[],[f84,f110])).
% 1.32/0.56  fof(f110,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3) | ~spl7_3),
% 1.32/0.56    inference(avatar_component_clause,[],[f108])).
% 1.32/0.56  fof(f34,plain,(
% 1.32/0.56    sK0 != sK3),
% 1.32/0.56    inference(cnf_transformation,[],[f26])).
% 1.32/0.56  fof(f260,plain,(
% 1.32/0.56    sK0 = sK1 | ~spl7_3),
% 1.32/0.56    inference(resolution,[],[f222,f86])).
% 1.32/0.56  fof(f222,plain,(
% 1.32/0.56    ( ! [X3] : (~r2_hidden(X3,k2_tarski(sK0,sK1)) | sK1 = X3) ) | ~spl7_3),
% 1.32/0.56    inference(backward_demodulation,[],[f195,f206])).
% 1.32/0.56  fof(f195,plain,(
% 1.32/0.56    ( ! [X3] : (~r2_hidden(X3,k2_tarski(sK0,sK1)) | sK3 = X3) ) | ~spl7_3),
% 1.32/0.56    inference(duplicate_literal_removal,[],[f189])).
% 1.32/0.56  fof(f189,plain,(
% 1.32/0.56    ( ! [X3] : (~r2_hidden(X3,k2_tarski(sK0,sK1)) | sK3 = X3 | sK3 = X3) ) | ~spl7_3),
% 1.32/0.56    inference(superposition,[],[f87,f110])).
% 1.32/0.56  fof(f176,plain,(
% 1.32/0.56    ~spl7_2 | spl7_4),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f175])).
% 1.32/0.56  fof(f175,plain,(
% 1.32/0.56    $false | (~spl7_2 | spl7_4)),
% 1.32/0.56    inference(subsumption_resolution,[],[f160,f164])).
% 1.32/0.56  fof(f164,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) | ~spl7_2),
% 1.32/0.56    inference(backward_demodulation,[],[f140,f159])).
% 1.32/0.56  fof(f159,plain,(
% 1.32/0.56    sK1 = sK2 | ~spl7_2),
% 1.32/0.56    inference(subsumption_resolution,[],[f158,f33])).
% 1.32/0.56  fof(f158,plain,(
% 1.32/0.56    sK1 = sK2 | sK0 = sK2 | ~spl7_2),
% 1.32/0.56    inference(resolution,[],[f136,f87])).
% 1.32/0.56  fof(f136,plain,(
% 1.32/0.56    r2_hidden(sK2,k2_tarski(sK0,sK1)) | ~spl7_2),
% 1.32/0.56    inference(superposition,[],[f86,f106])).
% 1.32/0.56  fof(f106,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | ~spl7_2),
% 1.32/0.56    inference(avatar_component_clause,[],[f104])).
% 1.32/0.56  fof(f140,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK1) | ~spl7_2),
% 1.32/0.56    inference(backward_demodulation,[],[f106,f139])).
% 1.32/0.56  fof(f139,plain,(
% 1.32/0.56    sK1 = sK3 | ~spl7_2),
% 1.32/0.56    inference(subsumption_resolution,[],[f138,f34])).
% 1.32/0.56  fof(f138,plain,(
% 1.32/0.56    sK1 = sK3 | sK0 = sK3 | ~spl7_2),
% 1.32/0.56    inference(resolution,[],[f135,f87])).
% 1.32/0.56  fof(f135,plain,(
% 1.32/0.56    r2_hidden(sK3,k2_tarski(sK0,sK1)) | ~spl7_2),
% 1.32/0.56    inference(superposition,[],[f84,f106])).
% 1.32/0.56  fof(f160,plain,(
% 1.32/0.56    k2_tarski(sK0,sK1) != k2_tarski(sK1,sK1) | (~spl7_2 | spl7_4)),
% 1.32/0.56    inference(backward_demodulation,[],[f113,f159])).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (16819)------------------------------
% 1.32/0.56  % (16819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (16819)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (16819)Memory used [KB]: 6268
% 1.32/0.56  % (16819)Time elapsed: 0.131 s
% 1.32/0.56  % (16819)------------------------------
% 1.32/0.56  % (16819)------------------------------
% 1.32/0.56  % (16810)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.56  % (16791)Success in time 0.189 s
%------------------------------------------------------------------------------
