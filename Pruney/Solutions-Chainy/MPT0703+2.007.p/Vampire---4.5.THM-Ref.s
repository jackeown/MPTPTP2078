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
% DateTime   : Thu Dec  3 12:54:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 132 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  191 ( 381 expanded)
%              Number of equality atoms :   41 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f89,f120,f131,f142,f216,f417])).

fof(f417,plain,
    ( ~ spl3_18
    | ~ spl3_5
    | ~ spl3_7
    | spl3_10 ),
    inference(avatar_split_clause,[],[f410,f128,f85,f63,f212])).

fof(f212,plain,
    ( spl3_18
  <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f63,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( spl3_7
  <=> k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f128,plain,
    ( spl3_10
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f410,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_7
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f65,f130,f256,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f256,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f240,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f36,f30])).

% (30262)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f240,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2)))
    | ~ spl3_7 ),
    inference(superposition,[],[f231,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f231,plain,
    ( ! [X6] : r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X6))
    | ~ spl3_7 ),
    inference(superposition,[],[f92,f87])).

fof(f87,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f92,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(unit_resulting_resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f130,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f216,plain,
    ( spl3_18
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f207,f140,f110,f212])).

fof(f110,plain,
    ( spl3_8
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f140,plain,
    ( spl3_11
  <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f207,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f112,f141])).

fof(f141,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f112,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f142,plain,
    ( ~ spl3_5
    | spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f138,f58,f140,f63])).

fof(f58,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f38,f60])).

fof(f60,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f131,plain,
    ( ~ spl3_10
    | spl3_1 ),
    inference(avatar_split_clause,[],[f124,f43,f128])).

fof(f43,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f124,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f45,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f45,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f120,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f106,f53,f110])).

fof(f53,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f106,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f48,f85])).

fof(f48,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f75,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f66,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).

fof(f21,plain,
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

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f61,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f43])).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:04:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (30254)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.43  % (30255)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.44  % (30261)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.44  % (30253)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.46  % (30259)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.46  % (30256)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (30263)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.46  % (30251)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (30267)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (30260)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (30252)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (30257)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (30257)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f418,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f89,f120,f131,f142,f216,f417])).
% 0.22/0.48  fof(f417,plain,(
% 0.22/0.48    ~spl3_18 | ~spl3_5 | ~spl3_7 | spl3_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f410,f128,f85,f63,f212])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    spl3_18 <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl3_5 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl3_7 <=> k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl3_10 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f410,plain,(
% 0.22/0.48    k1_xboole_0 != k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl3_5 | ~spl3_7 | spl3_10)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f65,f130,f256,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.22/0.48  fof(f256,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_7),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f240,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f36,f30])).
% 0.22/0.48  % (30262)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.48  fof(f240,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2)))) ) | ~spl3_7),
% 0.22/0.48    inference(superposition,[],[f231,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f231,plain,(
% 0.22/0.48    ( ! [X6] : (r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X6))) ) | ~spl3_7),
% 0.22/0.48    inference(superposition,[],[f92,f87])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f85])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f29,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f128])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f216,plain,(
% 0.22/0.48    spl3_18 | ~spl3_8 | ~spl3_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f207,f140,f110,f212])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl3_8 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    spl3_11 <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl3_8 | ~spl3_11)),
% 0.22/0.48    inference(superposition,[],[f112,f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f140])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f110])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ~spl3_5 | spl3_11 | ~spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f138,f58,f140,f63])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl3_4 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) ) | ~spl3_4),
% 0.22/0.48    inference(resolution,[],[f38,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    v1_funct_1(sK2) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ~spl3_10 | spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f124,f43,f128])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f45,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f34,f30])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.48    inference(nnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f43])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl3_8 | ~spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f106,f53,f110])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 0.22/0.48    inference(resolution,[],[f39,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f35,f30])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    spl3_7 | ~spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f75,f48,f85])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 0.22/0.48    inference(resolution,[],[f33,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f63])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f58])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f53])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f48])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f43])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ~r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (30257)------------------------------
% 0.22/0.48  % (30257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30257)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (30257)Memory used [KB]: 6396
% 0.22/0.48  % (30257)Time elapsed: 0.068 s
% 0.22/0.48  % (30257)------------------------------
% 0.22/0.48  % (30257)------------------------------
% 0.22/0.49  % (30258)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (30265)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (30266)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (30250)Success in time 0.129 s
%------------------------------------------------------------------------------
