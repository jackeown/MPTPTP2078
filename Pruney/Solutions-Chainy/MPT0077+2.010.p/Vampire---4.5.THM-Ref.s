%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 169 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 ( 421 expanded)
%              Number of equality atoms :   28 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f871,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f70,f102,f108,f121,f464,f627,f629,f869])).

fof(f869,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f868,f625,f476,f51,f47])).

fof(f47,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f476,plain,
    ( spl3_12
  <=> k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f625,plain,
    ( spl3_24
  <=> k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f868,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f867])).

fof(f867,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f857,f477])).

fof(f477,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f476])).

fof(f857,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_xboole_0)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(superposition,[],[f459,f626])).

% (30753)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f626,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f625])).

fof(f459,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k3_xboole_0(sK0,X7)
        | r1_xboole_0(sK0,k2_xboole_0(sK1,X7)) )
    | ~ spl3_3 ),
    inference(superposition,[],[f38,f449])).

fof(f449,plain,
    ( ! [X8] : k3_xboole_0(sK0,k2_xboole_0(sK1,X8)) = k3_xboole_0(sK0,X8)
    | ~ spl3_3 ),
    inference(resolution,[],[f194,f52])).

fof(f52,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(forward_demodulation,[],[f184,f72])).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f35,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f629,plain,
    ( ~ spl3_3
    | spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f568,f462,f476,f51])).

fof(f462,plain,
    ( spl3_11
  <=> k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f568,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f463,f37])).

fof(f463,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f462])).

fof(f627,plain,
    ( spl3_24
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f606,f44,f625])).

fof(f44,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f606,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f450,f30])).

fof(f450,plain,
    ( ! [X9] : k3_xboole_0(sK0,k2_xboole_0(sK2,X9)) = k3_xboole_0(sK0,X9)
    | ~ spl3_1 ),
    inference(resolution,[],[f194,f45])).

fof(f45,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f464,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f451,f51,f462])).

fof(f451,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f449,f30])).

fof(f121,plain,
    ( ~ spl3_2
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl3_2
    | spl3_6 ),
    inference(subsumption_resolution,[],[f48,f118])).

fof(f118,plain,
    ( ! [X1] : ~ r1_xboole_0(sK0,k2_xboole_0(X1,sK2))
    | spl3_6 ),
    inference(resolution,[],[f114,f75])).

fof(f75,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f114,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ r1_xboole_0(sK0,X2) )
    | spl3_6 ),
    inference(resolution,[],[f109,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK0)
        | ~ r1_tarski(sK2,X0) )
    | spl3_6 ),
    inference(resolution,[],[f107,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f107,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_6
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f48,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f108,plain,
    ( ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f104,f44,f106])).

fof(f104,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl3_1 ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f102,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f48,f98])).

fof(f98,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | spl3_5 ),
    inference(resolution,[],[f95,f34])).

fof(f95,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK1,X2)
        | ~ r1_xboole_0(sK0,X2) )
    | spl3_5 ),
    inference(resolution,[],[f91,f36])).

fof(f91,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(X3,sK0)
        | ~ r1_tarski(sK1,X3) )
    | spl3_5 ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_5
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f65,f51,f68])).

fof(f65,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl3_3 ),
    inference(resolution,[],[f36,f55])).

fof(f55,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f57,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f44,f51,f47])).

fof(f24,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f53,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f28,f47,f51])).

fof(f28,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f29,f47,f44])).

fof(f29,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:10:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (30746)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (30755)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (30747)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (30743)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (30745)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (30760)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (30754)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (30746)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f871,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f49,f53,f57,f70,f102,f108,f121,f464,f627,f629,f869])).
% 0.22/0.51  fof(f869,plain,(
% 0.22/0.51    spl3_2 | ~spl3_3 | ~spl3_12 | ~spl3_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f868,f625,f476,f51,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl3_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f476,plain,(
% 0.22/0.51    spl3_12 <=> k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.51  fof(f625,plain,(
% 0.22/0.51    spl3_24 <=> k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.51  fof(f868,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_12 | ~spl3_24)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f867])).
% 0.22/0.51  fof(f867,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_12 | ~spl3_24)),
% 0.22/0.51    inference(forward_demodulation,[],[f857,f477])).
% 0.22/0.51  fof(f477,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) | ~spl3_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f476])).
% 0.22/0.51  fof(f857,plain,(
% 0.22/0.51    k1_xboole_0 != k3_xboole_0(sK0,k1_xboole_0) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_24)),
% 0.22/0.51    inference(superposition,[],[f459,f626])).
% 0.22/0.51  % (30753)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  fof(f626,plain,(
% 0.22/0.51    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) | ~spl3_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f625])).
% 0.22/0.51  fof(f459,plain,(
% 0.22/0.51    ( ! [X7] : (k1_xboole_0 != k3_xboole_0(sK0,X7) | r1_xboole_0(sK0,k2_xboole_0(sK1,X7))) ) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f38,f449])).
% 0.22/0.51  fof(f449,plain,(
% 0.22/0.51    ( ! [X8] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X8)) = k3_xboole_0(sK0,X8)) ) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f194,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f184,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.51    inference(superposition,[],[f35,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(superposition,[],[f39,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f629,plain,(
% 0.22/0.51    ~spl3_3 | spl3_12 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f568,f462,f476,f51])).
% 0.22/0.51  fof(f462,plain,(
% 0.22/0.51    spl3_11 <=> k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f568,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) | ~r1_xboole_0(sK0,sK1) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f463,f37])).
% 0.22/0.51  fof(f463,plain,(
% 0.22/0.51    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f462])).
% 0.22/0.51  fof(f627,plain,(
% 0.22/0.51    spl3_24 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f606,f44,f625])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f606,plain,(
% 0.22/0.51    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.51    inference(superposition,[],[f450,f30])).
% 0.22/0.51  fof(f450,plain,(
% 0.22/0.51    ( ! [X9] : (k3_xboole_0(sK0,k2_xboole_0(sK2,X9)) = k3_xboole_0(sK0,X9)) ) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f194,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f464,plain,(
% 0.22/0.51    spl3_11 | ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f451,f51,f462])).
% 0.22/0.51  fof(f451,plain,(
% 0.22/0.51    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f449,f30])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ~spl3_2 | spl3_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    $false | (~spl3_2 | spl3_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f48,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_xboole_0(sK0,k2_xboole_0(X1,sK2))) ) | spl3_6),
% 0.22/0.51    inference(resolution,[],[f114,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 0.22/0.51    inference(superposition,[],[f34,f35])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X2] : (~r1_tarski(sK2,X2) | ~r1_xboole_0(sK0,X2)) ) | spl3_6),
% 0.22/0.51    inference(resolution,[],[f109,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_xboole_0(X0,sK0) | ~r1_tarski(sK2,X0)) ) | spl3_6),
% 0.22/0.51    inference(resolution,[],[f107,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ~r1_xboole_0(sK2,sK0) | spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl3_6 <=> r1_xboole_0(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f47])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ~spl3_6 | spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f104,f44,f106])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~r1_xboole_0(sK2,sK0) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f56,f36])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ~spl3_2 | spl3_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    $false | (~spl3_2 | spl3_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f48,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | spl3_5),
% 0.22/0.51    inference(resolution,[],[f95,f34])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X2] : (~r1_tarski(sK1,X2) | ~r1_xboole_0(sK0,X2)) ) | spl3_5),
% 0.22/0.51    inference(resolution,[],[f91,f36])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X3] : (~r1_xboole_0(X3,sK0) | ~r1_tarski(sK1,X3)) ) | spl3_5),
% 0.22/0.51    inference(resolution,[],[f41,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ~r1_xboole_0(sK1,sK0) | spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl3_5 <=> r1_xboole_0(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~spl3_5 | spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f51,f68])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ~r1_xboole_0(sK1,sK0) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f36,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~spl3_2 | ~spl3_3 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f44,f51,f47])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.51    inference(negated_conjecture,[],[f11])).
% 0.22/0.51  fof(f11,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl3_3 | spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f47,f51])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl3_1 | spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f29,f47,f44])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (30746)------------------------------
% 0.22/0.51  % (30746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30746)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (30746)Memory used [KB]: 11001
% 0.22/0.51  % (30746)Time elapsed: 0.072 s
% 0.22/0.51  % (30746)------------------------------
% 0.22/0.51  % (30746)------------------------------
% 0.22/0.51  % (30739)Success in time 0.151 s
%------------------------------------------------------------------------------
