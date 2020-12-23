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
% DateTime   : Thu Dec  3 12:54:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 127 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  184 ( 374 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f245,f290,f375,f432,f1498,f1576])).

fof(f1576,plain,
    ( spl3_33
    | ~ spl3_41
    | ~ spl3_67 ),
    inference(avatar_contradiction_clause,[],[f1575])).

fof(f1575,plain,
    ( $false
    | spl3_33
    | ~ spl3_41
    | ~ spl3_67 ),
    inference(global_subsumption,[],[f374,f1500])).

fof(f1500,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_41
    | ~ spl3_67 ),
    inference(superposition,[],[f431,f1497])).

fof(f1497,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f1496,plain,
    ( spl3_67
  <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f431,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl3_41
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f374,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl3_33
  <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1498,plain,
    ( spl3_67
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f849,f43,f38,f1496])).

fof(f38,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f849,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f40,f45,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f45,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f40,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f432,plain,
    ( spl3_41
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f106,f58,f429])).

fof(f58,plain,
    ( spl3_5
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f106,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f60,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f375,plain,
    ( ~ spl3_33
    | ~ spl3_1
    | spl3_24
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f297,f288,f242,f38,f372])).

fof(f242,plain,
    ( spl3_24
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f288,plain,
    ( spl3_28
  <=> ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f297,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_1
    | spl3_24
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f40,f244,f289,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f289,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f288])).

fof(f244,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f242])).

fof(f290,plain,
    ( spl3_28
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f265,f53,f288])).

fof(f53,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f265,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f55,f75])).

fof(f75,plain,(
    ! [X2,X3,X1] :
      ( r1_tarski(k6_subset_1(X1,X2),X3)
      | ~ r1_tarski(X1,X3) ) ),
    inference(superposition,[],[f32,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(k6_subset_1(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f55,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f245,plain,
    ( ~ spl3_24
    | spl3_3 ),
    inference(avatar_split_clause,[],[f219,f48,f242])).

fof(f48,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f219,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f50,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f61,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:35:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.42  % (27094)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.45  % (27080)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (27094)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f1577,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f245,f290,f375,f432,f1498,f1576])).
% 0.19/0.45  fof(f1576,plain,(
% 0.19/0.45    spl3_33 | ~spl3_41 | ~spl3_67),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f1575])).
% 0.19/0.45  fof(f1575,plain,(
% 0.19/0.45    $false | (spl3_33 | ~spl3_41 | ~spl3_67)),
% 0.19/0.45    inference(global_subsumption,[],[f374,f1500])).
% 0.19/0.45  fof(f1500,plain,(
% 0.19/0.45    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl3_41 | ~spl3_67)),
% 0.19/0.45    inference(superposition,[],[f431,f1497])).
% 0.19/0.45  fof(f1497,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_67),
% 0.19/0.45    inference(avatar_component_clause,[],[f1496])).
% 0.19/0.45  fof(f1496,plain,(
% 0.19/0.45    spl3_67 <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.19/0.45  fof(f431,plain,(
% 0.19/0.45    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_41),
% 0.19/0.45    inference(avatar_component_clause,[],[f429])).
% 0.19/0.45  fof(f429,plain,(
% 0.19/0.45    spl3_41 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.19/0.45  fof(f374,plain,(
% 0.19/0.45    k1_xboole_0 != k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | spl3_33),
% 0.19/0.45    inference(avatar_component_clause,[],[f372])).
% 0.19/0.45  fof(f372,plain,(
% 0.19/0.45    spl3_33 <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.19/0.45  fof(f1498,plain,(
% 0.19/0.45    spl3_67 | ~spl3_1 | ~spl3_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f849,f43,f38,f1496])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    spl3_1 <=> v1_relat_1(sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    spl3_2 <=> v1_funct_1(sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.45  fof(f849,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_2)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f40,f45,f33])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.45    inference(flattening,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.45    inference(ennf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    v1_funct_1(sK2) | ~spl3_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f43])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    v1_relat_1(sK2) | ~spl3_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f38])).
% 0.19/0.45  fof(f432,plain,(
% 0.19/0.45    spl3_41 | ~spl3_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f106,f58,f429])).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    spl3_5 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.45  fof(f106,plain,(
% 0.19/0.45    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_5),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f60,f35])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f31,f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.45    inference(nnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f58])).
% 0.19/0.45  fof(f375,plain,(
% 0.19/0.45    ~spl3_33 | ~spl3_1 | spl3_24 | ~spl3_28),
% 0.19/0.45    inference(avatar_split_clause,[],[f297,f288,f242,f38,f372])).
% 0.19/0.45  fof(f242,plain,(
% 0.19/0.45    spl3_24 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.19/0.45  fof(f288,plain,(
% 0.19/0.45    spl3_28 <=> ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.19/0.45  fof(f297,plain,(
% 0.19/0.45    k1_xboole_0 != k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl3_1 | spl3_24 | ~spl3_28)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f40,f244,f289,f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.19/0.45    inference(flattening,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.19/0.45  fof(f289,plain,(
% 0.19/0.45    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_28),
% 0.19/0.45    inference(avatar_component_clause,[],[f288])).
% 0.19/0.45  fof(f244,plain,(
% 0.19/0.45    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_24),
% 0.19/0.45    inference(avatar_component_clause,[],[f242])).
% 0.19/0.45  fof(f290,plain,(
% 0.19/0.45    spl3_28 | ~spl3_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f265,f53,f288])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.45  fof(f265,plain,(
% 0.19/0.45    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_4),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f55,f75])).
% 0.19/0.45  fof(f75,plain,(
% 0.19/0.45    ( ! [X2,X3,X1] : (r1_tarski(k6_subset_1(X1,X2),X3) | ~r1_tarski(X1,X3)) )),
% 0.19/0.45    inference(superposition,[],[f32,f63])).
% 0.19/0.45  fof(f63,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_xboole_0(k6_subset_1(X0,X1),X0) = X0) )),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f34,f29])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f26,f27])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.19/0.45  fof(f55,plain,(
% 0.19/0.45    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f53])).
% 0.19/0.45  fof(f245,plain,(
% 0.19/0.45    ~spl3_24 | spl3_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f219,f48,f242])).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.45  fof(f219,plain,(
% 0.19/0.45    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_3),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f50,f36])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f30,f27])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    ~r1_tarski(sK0,sK1) | spl3_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f48])).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    spl3_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f23,f58])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.45    inference(flattening,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.19/0.45    inference(ennf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.19/0.45    inference(negated_conjecture,[],[f8])).
% 0.19/0.45  fof(f8,conjecture,(
% 0.19/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.19/0.45  fof(f56,plain,(
% 0.19/0.45    spl3_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f24,f53])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ~spl3_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f25,f48])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ~r1_tarski(sK0,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    spl3_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f22,f43])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    v1_funct_1(sK2)),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    spl3_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f21,f38])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    v1_relat_1(sK2)),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (27094)------------------------------
% 0.19/0.45  % (27094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (27094)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (27094)Memory used [KB]: 11641
% 0.19/0.45  % (27094)Time elapsed: 0.062 s
% 0.19/0.45  % (27094)------------------------------
% 0.19/0.45  % (27094)------------------------------
% 0.19/0.45  % (27077)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.45  % (27076)Success in time 0.108 s
%------------------------------------------------------------------------------
