%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  92 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 220 expanded)
%              Number of equality atoms :   30 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f169,f171,f178,f180,f211])).

fof(f211,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f191,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).

fof(f191,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(resolution,[],[f168,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f168,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_3
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f180,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f177,f21])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f177,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f178,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f173,f158,f175,f162])).

fof(f162,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f158,plain,
    ( spl3_1
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f173,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f160,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f160,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f158])).

fof(f171,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f164,f20])).

fof(f164,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f162])).

fof(f169,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f156,f166,f162,f158])).

fof(f156,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k9_relat_1(k8_relat_1(sK0,sK2),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f31,f100])).

fof(f100,plain,(
    ! [X10,X11,X9] :
      ( k9_relat_1(k8_relat_1(X9,X10),X11) = k1_setfam_1(k2_tarski(X9,k9_relat_1(X10,X11)))
      | ~ v1_relat_1(k8_relat_1(X9,X10))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k7_relat_1(X10,X11)) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X10,X11,X9] :
      ( k9_relat_1(k8_relat_1(X9,X10),X11) = k1_setfam_1(k2_tarski(X9,k9_relat_1(X10,X11)))
      | ~ v1_relat_1(k8_relat_1(X9,X10))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k7_relat_1(X10,X11))
      | ~ v1_relat_1(X10) ) ),
    inference(superposition,[],[f46,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k2_tarski(X2,k9_relat_1(X0,X1)))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f35,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(k2_tarski(X3,k2_relat_1(X2))) = k2_relat_1(k8_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k8_relat_1(X0,X1),X2) = k2_relat_1(k8_relat_1(X0,k7_relat_1(X1,X2)))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f26,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f31,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK2,sK1))) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (7893)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.45  % (7893)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f212,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f169,f171,f178,f180,f211])).
% 0.22/0.45  fof(f211,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f210])).
% 0.22/0.45  fof(f210,plain,(
% 0.22/0.45    $false | spl3_3),
% 0.22/0.45    inference(resolution,[],[f191,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.45    inference(resolution,[],[f168,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.45  fof(f168,plain,(
% 0.22/0.45    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f166])).
% 0.22/0.45  fof(f166,plain,(
% 0.22/0.45    spl3_3 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f180,plain,(
% 0.22/0.45    spl3_4),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f179])).
% 0.22/0.45  fof(f179,plain,(
% 0.22/0.45    $false | spl3_4),
% 0.22/0.45    inference(resolution,[],[f177,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    v1_funct_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f177,plain,(
% 0.22/0.45    ~v1_funct_1(sK2) | spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f175])).
% 0.22/0.45  fof(f175,plain,(
% 0.22/0.45    spl3_4 <=> v1_funct_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f178,plain,(
% 0.22/0.45    ~spl3_2 | ~spl3_4 | spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f173,f158,f175,f162])).
% 0.22/0.45  fof(f162,plain,(
% 0.22/0.45    spl3_2 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f158,plain,(
% 0.22/0.45    spl3_1 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.45    inference(resolution,[],[f160,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.22/0.45  fof(f160,plain,(
% 0.22/0.45    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f158])).
% 0.22/0.45  fof(f171,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.45  fof(f170,plain,(
% 0.22/0.45    $false | spl3_2),
% 0.22/0.45    inference(resolution,[],[f164,f20])).
% 0.22/0.45  fof(f164,plain,(
% 0.22/0.45    ~v1_relat_1(sK2) | spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f162])).
% 0.22/0.45  fof(f169,plain,(
% 0.22/0.45    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f156,f166,f162,f158])).
% 0.22/0.45  fof(f156,plain,(
% 0.22/0.45    ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f155])).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k9_relat_1(k8_relat_1(sK0,sK2),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.22/0.45    inference(superposition,[],[f31,f100])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    ( ! [X10,X11,X9] : (k9_relat_1(k8_relat_1(X9,X10),X11) = k1_setfam_1(k2_tarski(X9,k9_relat_1(X10,X11))) | ~v1_relat_1(k8_relat_1(X9,X10)) | ~v1_relat_1(X10) | ~v1_relat_1(k7_relat_1(X10,X11))) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.45  fof(f95,plain,(
% 0.22/0.45    ( ! [X10,X11,X9] : (k9_relat_1(k8_relat_1(X9,X10),X11) = k1_setfam_1(k2_tarski(X9,k9_relat_1(X10,X11))) | ~v1_relat_1(k8_relat_1(X9,X10)) | ~v1_relat_1(X10) | ~v1_relat_1(k7_relat_1(X10,X11)) | ~v1_relat_1(X10)) )),
% 0.22/0.45    inference(superposition,[],[f46,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k2_tarski(X2,k9_relat_1(X0,X1))) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(superposition,[],[f35,f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X3,k2_relat_1(X2))) = k2_relat_1(k8_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(superposition,[],[f33,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f23,f24,f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f27,f24])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k9_relat_1(k8_relat_1(X0,X1),X2) = k2_relat_1(k8_relat_1(X0,k7_relat_1(X1,X2))) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(superposition,[],[f26,f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k2_tarski(sK0,k9_relat_1(sK2,sK1)))),
% 0.22/0.45    inference(definition_unfolding,[],[f22,f24])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (7893)------------------------------
% 0.22/0.45  % (7893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (7893)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (7893)Memory used [KB]: 6268
% 0.22/0.45  % (7893)Time elapsed: 0.014 s
% 0.22/0.45  % (7893)------------------------------
% 0.22/0.45  % (7893)------------------------------
% 0.22/0.46  % (7888)Success in time 0.098 s
%------------------------------------------------------------------------------
