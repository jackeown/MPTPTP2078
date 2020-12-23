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
% DateTime   : Thu Dec  3 12:49:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 142 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 ( 433 expanded)
%              Number of equality atoms :   62 ( 171 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f46,f106,f109,f119,f127])).

fof(f127,plain,
    ( spl2_2
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl2_2
    | ~ spl2_8 ),
    inference(resolution,[],[f123,f43])).

fof(f43,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f123,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_8 ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_8 ),
    inference(superposition,[],[f97,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl2_8
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f97,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X2))
      | r1_xboole_0(k1_relat_1(sK1),X2) ) ),
    inference(superposition,[],[f35,f85])).

fof(f85,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f119,plain,
    ( ~ spl2_7
    | spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f114,f38,f116,f103])).

fof(f103,plain,
    ( spl2_7
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f38,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f25,f47])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f109,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f107,f21])).

fof(f107,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_7 ),
    inference(resolution,[],[f105,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f105,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f106,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f101,f42,f38,f103])).

fof(f101,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f100,f47])).

fof(f100,plain,
    ( k1_xboole_0 = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f24,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f85,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f23,f42,f38])).

fof(f23,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f22,f42,f38])).

fof(f22,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (14502)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.42  % (14502)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f128,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f45,f46,f106,f109,f119,f127])).
% 0.20/0.42  fof(f127,plain,(
% 0.20/0.42    spl2_2 | ~spl2_8),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f125])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    $false | (spl2_2 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f123,f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_8),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f120])).
% 0.20/0.42  fof(f120,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_8),
% 0.20/0.42    inference(superposition,[],[f97,f118])).
% 0.20/0.42  fof(f118,plain,(
% 0.20/0.42    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f116])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    spl2_8 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f97,plain,(
% 0.20/0.42    ( ! [X2] : (k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X2)) | r1_xboole_0(k1_relat_1(sK1),X2)) )),
% 0.20/0.42    inference(superposition,[],[f35,f85])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))) )),
% 0.20/0.42    inference(resolution,[],[f34,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f30,f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f32,f27])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.42  fof(f119,plain,(
% 0.20/0.42    ~spl2_7 | spl2_8 | ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f114,f38,f116,f103])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    spl2_7 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_1),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f113])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_1),
% 0.20/0.42    inference(superposition,[],[f49,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.20/0.42    inference(superposition,[],[f25,f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.20/0.42    inference(resolution,[],[f29,f21])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(nnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.42  fof(f108,plain,(
% 0.20/0.42    $false | spl2_7),
% 0.20/0.42    inference(resolution,[],[f107,f21])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | spl2_7),
% 0.20/0.42    inference(resolution,[],[f105,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f103])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    ~spl2_7 | spl2_1 | ~spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f101,f42,f38,f103])).
% 0.20/0.42  fof(f101,plain,(
% 0.20/0.42    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 0.20/0.42    inference(forward_demodulation,[],[f100,f47])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f99])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 0.20/0.42    inference(superposition,[],[f24,f91])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 0.20/0.42    inference(superposition,[],[f85,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) | ~spl2_2),
% 0.20/0.42    inference(resolution,[],[f36,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f42])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f31,f27])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ~spl2_1 | ~spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f42,f38])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl2_1 | spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f42,f38])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (14502)------------------------------
% 0.20/0.42  % (14502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (14502)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (14502)Memory used [KB]: 6140
% 0.20/0.42  % (14502)Time elapsed: 0.008 s
% 0.20/0.42  % (14502)------------------------------
% 0.20/0.42  % (14502)------------------------------
% 0.20/0.42  % (14495)Success in time 0.066 s
%------------------------------------------------------------------------------
