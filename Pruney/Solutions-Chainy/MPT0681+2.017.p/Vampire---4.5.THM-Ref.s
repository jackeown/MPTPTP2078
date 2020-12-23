%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  96 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 314 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f56,f64,f71,f76])).

fof(f76,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k9_relat_1(sK2,sK0) != k9_relat_1(sK2,sK0)
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f72,f55])).

fof(f55,plain,
    ( sK0 = k6_subset_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_6
  <=> sK0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( k9_relat_1(sK2,sK0) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f63,f70])).

fof(f70,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_8
  <=> ! [X1,X0] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f63,plain,
    ( k9_relat_1(sK2,sK0) != k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_7
  <=> k9_relat_1(sK2,sK0) = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f71,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f66,f35,f30,f25,f69])).

fof(f25,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f30,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f27,f32,f37,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f37,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f32,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f27,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f64,plain,
    ( ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f49,f45,f61])).

fof(f45,plain,
    ( spl3_5
  <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f49,plain,
    ( k9_relat_1(sK2,sK0) != k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f47,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f47,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f56,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f50,f40,f53])).

fof(f40,plain,
    ( spl3_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f50,plain,
    ( sK0 = k6_subset_1(sK0,sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f42,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f48,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f17,f45])).

fof(f17,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:17:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (5636)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.44  % (5636)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f56,f64,f71,f76])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ~spl3_6 | spl3_7 | ~spl3_8),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    $false | (~spl3_6 | spl3_7 | ~spl3_8)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    k9_relat_1(sK2,sK0) != k9_relat_1(sK2,sK0) | (~spl3_6 | spl3_7 | ~spl3_8)),
% 0.21/0.44    inference(forward_demodulation,[],[f72,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    sK0 = k6_subset_1(sK0,sK1) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl3_6 <=> sK0 = k6_subset_1(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    k9_relat_1(sK2,sK0) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | (spl3_7 | ~spl3_8)),
% 0.21/0.44    inference(superposition,[],[f63,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl3_8 <=> ! [X1,X0] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    k9_relat_1(sK2,sK0) != k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl3_7 <=> k9_relat_1(sK2,sK0) = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl3_8 | ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f66,f35,f30,f25,f69])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    spl3_2 <=> v1_funct_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    spl3_3 <=> v2_funct_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f27,f32,f37,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    v2_funct_1(sK2) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f35])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    v1_funct_1(sK2) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f30])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f25])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ~spl3_7 | spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f49,f45,f61])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl3_5 <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    k9_relat_1(sK2,sK0) != k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl3_5),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f47,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f20,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl3_6 | ~spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f50,f40,f53])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    spl3_4 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    sK0 = k6_subset_1(sK0,sK1) | ~spl3_4),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f42,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f19,f18])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f40])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f45])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f40])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    v2_funct_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    v1_funct_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (5636)------------------------------
% 0.21/0.44  % (5636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (5636)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (5636)Memory used [KB]: 10618
% 0.21/0.44  % (5636)Time elapsed: 0.030 s
% 0.21/0.44  % (5636)------------------------------
% 0.21/0.44  % (5636)------------------------------
% 0.21/0.44  % (5618)Success in time 0.084 s
%------------------------------------------------------------------------------
