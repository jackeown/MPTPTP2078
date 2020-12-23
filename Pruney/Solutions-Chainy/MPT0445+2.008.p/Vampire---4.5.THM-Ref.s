%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 109 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 239 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f48,f79,f128,f399,f463,f924,f1138])).

fof(f1138,plain,
    ( spl2_10
    | ~ spl2_20
    | ~ spl2_54 ),
    inference(avatar_contradiction_clause,[],[f1137])).

fof(f1137,plain,
    ( $false
    | spl2_10
    | ~ spl2_20
    | ~ spl2_54 ),
    inference(global_subsumption,[],[f462,f1092])).

fof(f1092,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | spl2_10
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f1069,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1069,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | spl2_10
    | ~ spl2_54 ),
    inference(superposition,[],[f127,f923])).

fof(f923,plain,
    ( ! [X0] : k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0)))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f922])).

fof(f922,plain,
    ( spl2_54
  <=> ! [X0] : k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f127,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_10
  <=> r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f462,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl2_20
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f924,plain,
    ( spl2_54
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f258,f46,f39,f922])).

fof(f39,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f46,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_subset_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f258,plain,
    ( ! [X0] : k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f41,f47,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k6_subset_1(sK0,X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f463,plain,
    ( spl2_20
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f440,f396,f460])).

fof(f396,plain,
    ( spl2_16
  <=> k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f440,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | ~ spl2_16 ),
    inference(superposition,[],[f85,f398])).

fof(f398,plain,
    ( k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f396])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f399,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f234,f39,f34,f396])).

fof(f34,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f234,plain,
    ( k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f41,f36,f21])).

fof(f36,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f128,plain,
    ( ~ spl2_10
    | spl2_9 ),
    inference(avatar_split_clause,[],[f81,f76,f125])).

fof(f76,plain,
    ( spl2_9
  <=> r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f81,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
    | spl2_9 ),
    inference(unit_resulting_resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f78,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f79,plain,(
    ~ spl2_9 ),
    inference(avatar_split_clause,[],[f20,f76])).

fof(f20,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(f48,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f43,f34,f46])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_subset_1(sK0,X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:02:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (23385)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (23385)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f1139,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f37,f42,f48,f79,f128,f399,f463,f924,f1138])).
% 0.21/0.46  fof(f1138,plain,(
% 0.21/0.46    spl2_10 | ~spl2_20 | ~spl2_54),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f1137])).
% 0.21/0.46  fof(f1137,plain,(
% 0.21/0.46    $false | (spl2_10 | ~spl2_20 | ~spl2_54)),
% 0.21/0.46    inference(global_subsumption,[],[f462,f1092])).
% 0.21/0.46  fof(f1092,plain,(
% 0.21/0.46    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) | (spl2_10 | ~spl2_54)),
% 0.21/0.46    inference(forward_demodulation,[],[f1069,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f24,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.46  fof(f1069,plain,(
% 0.21/0.46    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) | (spl2_10 | ~spl2_54)),
% 0.21/0.46    inference(superposition,[],[f127,f923])).
% 0.21/0.46  fof(f923,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0)))) ) | ~spl2_54),
% 0.21/0.46    inference(avatar_component_clause,[],[f922])).
% 0.21/0.46  fof(f922,plain,(
% 0.21/0.46    spl2_54 <=> ! [X0] : k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    ~r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) | spl2_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    spl2_10 <=> r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.46  fof(f462,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) | ~spl2_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f460])).
% 0.21/0.46  fof(f460,plain,(
% 0.21/0.46    spl2_20 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.46  fof(f924,plain,(
% 0.21/0.46    spl2_54 | ~spl2_2 | ~spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f258,f46,f39,f922])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl2_3 <=> ! [X0] : v1_relat_1(k6_subset_1(sK0,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f258,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0)))) ) | (~spl2_2 | ~spl2_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f41,f47,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_subset_1(sK0,X0))) ) | ~spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f463,plain,(
% 0.21/0.46    spl2_20 | ~spl2_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f440,f396,f460])).
% 0.21/0.46  fof(f396,plain,(
% 0.21/0.46    spl2_16 <=> k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.46  fof(f440,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) | ~spl2_16),
% 0.21/0.46    inference(superposition,[],[f85,f398])).
% 0.21/0.46  fof(f398,plain,(
% 0.21/0.46    k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) | ~spl2_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f396])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f28,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f27,f23])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f22,f23])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.46  fof(f399,plain,(
% 0.21/0.46    spl2_16 | ~spl2_1 | ~spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f234,f39,f34,f396])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) | (~spl2_1 | ~spl2_2)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f41,f36,f21])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ~spl2_10 | spl2_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f81,f76,f125])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl2_9 <=> r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ~r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) | spl2_9),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f78,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f26,f23])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) | spl2_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f76])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ~spl2_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f76])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl2_3 | ~spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f43,f34,f46])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_subset_1(sK0,X0))) ) | ~spl2_1),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f25,f23])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f39])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f34])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    v1_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (23385)------------------------------
% 0.21/0.46  % (23385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23385)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (23385)Memory used [KB]: 12537
% 0.21/0.46  % (23385)Time elapsed: 0.042 s
% 0.21/0.46  % (23385)------------------------------
% 0.21/0.46  % (23385)------------------------------
% 0.21/0.46  % (23367)Success in time 0.097 s
%------------------------------------------------------------------------------
