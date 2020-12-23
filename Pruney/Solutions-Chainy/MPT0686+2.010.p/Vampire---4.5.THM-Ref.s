%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  86 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  123 ( 247 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f49,f58,f67,f72])).

fof(f72,plain,
    ( spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( k10_relat_1(sK0,sK1) != k10_relat_1(sK0,sK1)
    | spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f68,f56])).

fof(f56,plain,
    ( sK1 = k6_subset_1(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_6
  <=> sK1 = k6_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f68,plain,
    ( k10_relat_1(sK0,sK1) != k10_relat_1(sK0,k6_subset_1(sK1,sK2))
    | spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f48,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X1,X0] : k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f48,plain,
    ( k10_relat_1(sK0,sK1) != k6_subset_1(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_5
  <=> k10_relat_1(sK0,sK1) = k6_subset_1(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f67,plain,
    ( ~ spl3_4
    | spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f63,f35,f65,f40])).

fof(f40,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f35,plain,
    ( spl3_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
        | ~ v1_relat_1(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f21,f37])).

fof(f37,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f58,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f30,f54])).

fof(f30,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( sK1 = k6_subset_1(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f49,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f44,f25,f46])).

fof(f25,plain,
    ( spl3_1
  <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( k10_relat_1(sK0,sK1) != k6_subset_1(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f40])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2,X1] :
        ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
        & r1_xboole_0(X1,X2) )
   => ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:09:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (17656)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (17659)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17659)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f49,f58,f67,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl3_5 | ~spl3_6 | ~spl3_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    $false | (spl3_5 | ~spl3_6 | ~spl3_7)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    k10_relat_1(sK0,sK1) != k10_relat_1(sK0,sK1) | (spl3_5 | ~spl3_6 | ~spl3_7)),
% 0.21/0.47    inference(forward_demodulation,[],[f68,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    sK1 = k6_subset_1(sK1,sK2) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl3_6 <=> sK1 = k6_subset_1(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    k10_relat_1(sK0,sK1) != k10_relat_1(sK0,k6_subset_1(sK1,sK2)) | (spl3_5 | ~spl3_7)),
% 0.21/0.47    inference(superposition,[],[f48,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_7 <=> ! [X1,X0] : k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    k10_relat_1(sK0,sK1) != k6_subset_1(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl3_5 <=> k10_relat_1(sK0,sK1) = k6_subset_1(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ~spl3_4 | spl3_7 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f63,f35,f65,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl3_4 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl3_3 <=> v1_funct_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k10_relat_1(sK0,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) | ~v1_relat_1(sK0)) ) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f21,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    v1_funct_1(sK0) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_6 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f52,f30,f54])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    sK1 = k6_subset_1(sK1,sK2) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f23,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f30])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f19,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~spl3_5 | spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f25,f46])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    spl3_1 <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    k10_relat_1(sK0,sK1) != k6_subset_1(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | spl3_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f27,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f18])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f25])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f40])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f35])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f25])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (17659)------------------------------
% 0.21/0.47  % (17659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17659)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (17659)Memory used [KB]: 6140
% 0.21/0.47  % (17659)Time elapsed: 0.054 s
% 0.21/0.47  % (17659)------------------------------
% 0.21/0.47  % (17659)------------------------------
% 0.21/0.47  % (17653)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (17652)Success in time 0.114 s
%------------------------------------------------------------------------------
