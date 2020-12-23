%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  132 ( 202 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f48,f96,f101,f107,f165,f204,f208,f234])).

fof(f234,plain,
    ( ~ spl3_2
    | spl3_28
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl3_2
    | spl3_28
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f203,f211])).

fof(f211,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X0,X1)))
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(superposition,[],[f31,f207])).

fof(f207,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_29
  <=> ! [X1,X0] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f31,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f203,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_28
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f208,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f196,f163,f25,f206])).

fof(f25,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f163,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f196,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_24 ),
    inference(resolution,[],[f164,f27])).

fof(f27,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f163])).

fof(f204,plain,
    ( ~ spl3_28
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_14
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f199,f163,f104,f46,f34,f25,f201])).

fof(f34,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f46,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f104,plain,
    ( spl3_14
  <=> r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f199,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_14
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f198,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f198,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,sK0)))
    | ~ spl3_1
    | ~ spl3_5
    | spl3_14
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f197,f47])).

fof(f47,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f197,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | ~ spl3_1
    | spl3_14
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f106,f196])).

fof(f106,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1))))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f165,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f20,f163])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f107,plain,
    ( ~ spl3_14
    | ~ spl3_12
    | spl3_13 ),
    inference(avatar_split_clause,[],[f102,f98,f94,f104])).

fof(f94,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k6_subset_1(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f98,plain,
    ( spl3_13
  <=> r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f102,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1))))
    | ~ spl3_12
    | spl3_13 ),
    inference(resolution,[],[f100,f95])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k6_subset_1(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f100,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f101,plain,(
    ~ spl3_13 ),
    inference(avatar_split_clause,[],[f15,f98])).

fof(f15,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(f96,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f23,f94])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f36,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (16447)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (16447)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f235,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f28,f32,f36,f48,f96,f101,f107,f165,f204,f208,f234])).
% 0.21/0.44  fof(f234,plain,(
% 0.21/0.44    ~spl3_2 | spl3_28 | ~spl3_29),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.44  fof(f233,plain,(
% 0.21/0.44    $false | (~spl3_2 | spl3_28 | ~spl3_29)),
% 0.21/0.44    inference(subsumption_resolution,[],[f203,f211])).
% 0.21/0.44  fof(f211,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X0,X1)))) ) | (~spl3_2 | ~spl3_29)),
% 0.21/0.44    inference(superposition,[],[f31,f207])).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl3_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f206])).
% 0.21/0.44  fof(f206,plain,(
% 0.21/0.44    spl3_29 <=> ! [X1,X0] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    spl3_2 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f203,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK0,sK1))) | spl3_28),
% 0.21/0.44    inference(avatar_component_clause,[],[f201])).
% 0.21/0.44  fof(f201,plain,(
% 0.21/0.44    spl3_28 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.44  fof(f208,plain,(
% 0.21/0.44    spl3_29 | ~spl3_1 | ~spl3_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f196,f163,f25,f206])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    spl3_24 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_24)),
% 0.21/0.44    inference(resolution,[],[f164,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f25])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) | ~spl3_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f163])).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    ~spl3_28 | ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_14 | ~spl3_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f199,f163,f104,f46,f34,f25,f201])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl3_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    spl3_14 <=> r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK0,sK1))) | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_14 | ~spl3_24)),
% 0.21/0.44    inference(forward_demodulation,[],[f198,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f34])).
% 0.21/0.44  fof(f198,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,sK0))) | (~spl3_1 | ~spl3_5 | spl3_14 | ~spl3_24)),
% 0.21/0.44    inference(forward_demodulation,[],[f197,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f46])).
% 0.21/0.44  fof(f197,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) | (~spl3_1 | spl3_14 | ~spl3_24)),
% 0.21/0.44    inference(backward_demodulation,[],[f106,f196])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))) | spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f104])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    spl3_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f163])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ~spl3_14 | ~spl3_12 | spl3_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f102,f98,f94,f104])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl3_12 <=> ! [X1,X0,X2] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    spl3_13 <=> r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))) | (~spl3_12 | spl3_13)),
% 0.21/0.44    inference(resolution,[],[f100,f95])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f94])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl3_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f98])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ~spl3_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f98])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f94])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f21,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f46])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f19,f17])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f34])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f14,f25])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (16447)------------------------------
% 0.21/0.44  % (16447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (16447)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (16447)Memory used [KB]: 6268
% 0.21/0.44  % (16447)Time elapsed: 0.033 s
% 0.21/0.44  % (16447)------------------------------
% 0.21/0.44  % (16447)------------------------------
% 0.21/0.45  % (16439)Success in time 0.088 s
%------------------------------------------------------------------------------
