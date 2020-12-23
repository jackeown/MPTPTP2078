%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 195 expanded)
%              Number of leaves         :   41 (  84 expanded)
%              Depth                    :    8
%              Number of atoms          :  389 ( 601 expanded)
%              Number of equality atoms :   57 (  89 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1098,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f118,f124,f132,f202,f349,f405,f425,f584,f590,f844,f1012,f1088,f1091,f1095,f1097])).

fof(f1097,plain,
    ( k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4)
    | k1_xboole_0 != k1_relat_1(sK4)
    | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1095,plain,
    ( k1_xboole_0 != k2_relset_1(sK2,sK3,sK4)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k1_xboole_0 = k2_relat_1(sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1091,plain,
    ( ~ spl8_2
    | spl8_40
    | ~ spl8_57 ),
    inference(avatar_contradiction_clause,[],[f1090])).

fof(f1090,plain,
    ( $false
    | ~ spl8_2
    | spl8_40
    | ~ spl8_57 ),
    inference(subsumption_resolution,[],[f1089,f90])).

fof(f90,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1089,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_40
    | ~ spl8_57 ),
    inference(subsumption_resolution,[],[f1080,f589])).

fof(f589,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl8_57
  <=> r1_tarski(k2_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f1080,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl8_40 ),
    inference(superposition,[],[f423,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f423,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
    | spl8_40 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl8_40
  <=> r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f1088,plain,
    ( spl8_99
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f1079,f88,f1085])).

fof(f1085,plain,
    ( spl8_99
  <=> k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f1079,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f90,f78])).

fof(f1012,plain,
    ( spl8_92
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f1001,f88,f1009])).

fof(f1009,plain,
    ( spl8_92
  <=> k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f1001,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f90,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f844,plain,
    ( ~ spl8_78
    | ~ spl8_17
    | spl8_69 ),
    inference(avatar_split_clause,[],[f795,f681,f197,f791])).

fof(f791,plain,
    ( spl8_78
  <=> k1_xboole_0 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f197,plain,
    ( spl8_17
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f681,plain,
    ( spl8_69
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f795,plain,
    ( k1_xboole_0 != k2_relat_1(sK4)
    | ~ spl8_17
    | spl8_69 ),
    inference(unit_resulting_resolution,[],[f199,f683,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f683,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | spl8_69 ),
    inference(avatar_component_clause,[],[f681])).

fof(f199,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f197])).

fof(f590,plain,
    ( spl8_57
    | ~ spl8_17
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f585,f580,f197,f587])).

fof(f580,plain,
    ( spl8_56
  <=> v5_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f585,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ spl8_17
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f199,f582,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f582,plain,
    ( v5_relat_1(sK4,sK3)
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f580])).

fof(f584,plain,
    ( spl8_56
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f576,f88,f580])).

fof(f576,plain,
    ( v5_relat_1(sK4,sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f80,f90])).

% (6003)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (6003)Refutation not found, incomplete strategy% (6003)------------------------------
% (6003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6003)Termination reason: Refutation not found, incomplete strategy

% (6003)Memory used [KB]: 6140
% (6003)Time elapsed: 0.092 s
% (6003)------------------------------
% (6003)------------------------------
% (6007)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (6023)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (6012)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (6004)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (6021)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (6015)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (6004)Refutation not found, incomplete strategy% (6004)------------------------------
% (6004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6004)Termination reason: Refutation not found, incomplete strategy

% (6004)Memory used [KB]: 10618
% (6004)Time elapsed: 0.093 s
% (6004)------------------------------
% (6004)------------------------------
fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f425,plain,
    ( ~ spl8_40
    | spl8_37 ),
    inference(avatar_split_clause,[],[f409,f402,f421])).

fof(f402,plain,
    ( spl8_37
  <=> r2_hidden(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f409,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
    | spl8_37 ),
    inference(resolution,[],[f404,f220])).

fof(f220,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X2))
      | ~ r1_tarski(X3,X2) ) ),
    inference(subsumption_resolution,[],[f210,f55])).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f210,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_zfmisc_1(X2))
      | r2_hidden(X3,k1_zfmisc_1(X2))
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f65,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f404,plain,
    ( ~ r2_hidden(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | spl8_37 ),
    inference(avatar_component_clause,[],[f402])).

fof(f405,plain,
    ( ~ spl8_37
    | ~ spl8_8
    | spl8_31 ),
    inference(avatar_split_clause,[],[f397,f346,f121,f402])).

fof(f121,plain,
    ( spl8_8
  <=> r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f346,plain,
    ( spl8_31
  <=> sP0(k1_zfmisc_1(sK3),sK5(k2_relset_1(sK2,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f397,plain,
    ( ~ r2_hidden(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))
    | ~ spl8_8
    | spl8_31 ),
    inference(unit_resulting_resolution,[],[f123,f348,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ( r2_hidden(sK7(X0,X1),X0)
          & r2_hidden(X1,sK7(X0,X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X1,X3) )
     => ( r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(X1,sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X1,X3) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X2] :
      ( ( sP0(X0,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X3) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X2,X3) )
        | ~ sP0(X0,X2) ) ) ),
    inference(nnf_transformation,[],[f29])).

% (6022)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f29,plain,(
    ! [X0,X2] :
      ( sP0(X0,X2)
    <=> ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f348,plain,
    ( ~ sP0(k1_zfmisc_1(sK3),sK5(k2_relset_1(sK2,sK3,sK4)))
    | spl8_31 ),
    inference(avatar_component_clause,[],[f346])).

fof(f123,plain,
    ( r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f349,plain,
    ( ~ spl8_31
    | spl8_9 ),
    inference(avatar_split_clause,[],[f341,f128,f346])).

fof(f128,plain,
    ( spl8_9
  <=> r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f341,plain,
    ( ~ sP0(k1_zfmisc_1(sK3),sK5(k2_relset_1(sK2,sK3,sK4)))
    | spl8_9 ),
    inference(unit_resulting_resolution,[],[f130,f102,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X0,X3)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(X0,sK6(X0,X1))
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sP0(X0,sK6(X0,X1))
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X0,X2)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X0,X2)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(X0,sK6(X0,X1))
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sP0(X0,sK6(X0,X1))
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X0,X2) )
            & ( sP0(X0,X2)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f102,plain,(
    ! [X0] : sP1(k1_zfmisc_1(X0),X0) ),
    inference(superposition,[],[f81,f56])).

fof(f56,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f81,plain,(
    ! [X0] : sP1(X0,k3_tarski(X0)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP1(X0,X1) )
      & ( sP1(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f2,f30,f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f130,plain,
    ( ~ r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),sK3)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f202,plain,
    ( spl8_17
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f201,f88,f197])).

fof(f201,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f193,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f193,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | ~ spl8_2 ),
    inference(resolution,[],[f59,f90])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f132,plain,
    ( ~ spl8_9
    | spl8_6 ),
    inference(avatar_split_clause,[],[f126,f111,f128])).

fof(f111,plain,
    ( spl8_6
  <=> m1_subset_1(sK5(k2_relset_1(sK2,sK3,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f126,plain,
    ( ~ r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),sK3)
    | spl8_6 ),
    inference(resolution,[],[f113,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f113,plain,
    ( ~ m1_subset_1(sK5(k2_relset_1(sK2,sK3,sK4)),sK3)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f124,plain,
    ( spl8_8
    | spl8_7 ),
    inference(avatar_split_clause,[],[f119,f115,f121])).

fof(f115,plain,
    ( spl8_7
  <=> k1_xboole_0 = k2_relset_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f119,plain,
    ( r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f116,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f116,plain,
    ( k1_xboole_0 != k2_relset_1(sK2,sK3,sK4)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f118,plain,
    ( ~ spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f104,f115,f111])).

fof(f104,plain,
    ( k1_xboole_0 = k2_relset_1(sK2,sK3,sK4)
    | ~ m1_subset_1(sK5(k2_relset_1(sK2,sK3,sK4)),sK3) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,sK4))
      | ~ m1_subset_1(X3,sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,sK4))
        | ~ m1_subset_1(X3,sK3) )
    & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK2,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK2,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK2,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK2,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,X2))
              | ~ m1_subset_1(X3,sK3) )
          & k1_xboole_0 != k1_relset_1(sK2,sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,X2))
            | ~ m1_subset_1(X3,sK3) )
        & k1_xboole_0 != k1_relset_1(sK2,sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,sK4))
          | ~ m1_subset_1(X3,sK3) )
      & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f91,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f52,f88])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f53,f83])).

fof(f83,plain,
    ( spl8_1
  <=> k1_xboole_0 = k1_relset_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f53,plain,(
    k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:23:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (6008)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (6019)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (6017)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (6011)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (6009)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (6010)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (6005)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (6019)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f1098,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f86,f91,f118,f124,f132,f202,f349,f405,f425,f584,f590,f844,f1012,f1088,f1091,f1095,f1097])).
% 0.21/0.49  fof(f1097,plain,(
% 0.21/0.49    k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4) | k1_xboole_0 != k1_relat_1(sK4) | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f1095,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relset_1(sK2,sK3,sK4) | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) | k1_xboole_0 = k2_relat_1(sK4)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f1091,plain,(
% 0.21/0.49    ~spl8_2 | spl8_40 | ~spl8_57),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f1090])).
% 0.21/0.49  fof(f1090,plain,(
% 0.21/0.49    $false | (~spl8_2 | spl8_40 | ~spl8_57)),
% 0.21/0.49    inference(subsumption_resolution,[],[f1089,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl8_2 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f1089,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | (spl8_40 | ~spl8_57)),
% 0.21/0.49    inference(subsumption_resolution,[],[f1080,f589])).
% 0.21/0.49  fof(f589,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK4),sK3) | ~spl8_57),
% 0.21/0.49    inference(avatar_component_clause,[],[f587])).
% 0.21/0.49  fof(f587,plain,(
% 0.21/0.49    spl8_57 <=> r1_tarski(k2_relat_1(sK4),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 0.21/0.49  fof(f1080,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK4),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | spl8_40),
% 0.21/0.49    inference(superposition,[],[f423,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) | spl8_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f421])).
% 0.21/0.49  fof(f421,plain,(
% 0.21/0.49    spl8_40 <=> r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.21/0.49  fof(f1088,plain,(
% 0.21/0.49    spl8_99 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f1079,f88,f1085])).
% 0.21/0.49  fof(f1085,plain,(
% 0.21/0.49    spl8_99 <=> k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).
% 0.21/0.49  fof(f1079,plain,(
% 0.21/0.49    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) | ~spl8_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f90,f78])).
% 0.21/0.49  fof(f1012,plain,(
% 0.21/0.49    spl8_92 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f1001,f88,f1009])).
% 0.21/0.49  fof(f1009,plain,(
% 0.21/0.49    spl8_92 <=> k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).
% 0.21/0.49  fof(f1001,plain,(
% 0.21/0.49    k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) | ~spl8_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f90,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f844,plain,(
% 0.21/0.49    ~spl8_78 | ~spl8_17 | spl8_69),
% 0.21/0.49    inference(avatar_split_clause,[],[f795,f681,f197,f791])).
% 0.21/0.49  fof(f791,plain,(
% 0.21/0.49    spl8_78 <=> k1_xboole_0 = k2_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl8_17 <=> v1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.49  fof(f681,plain,(
% 0.21/0.49    spl8_69 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).
% 0.21/0.49  fof(f795,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(sK4) | (~spl8_17 | spl8_69)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f199,f683,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.49  fof(f683,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(sK4) | spl8_69),
% 0.21/0.49    inference(avatar_component_clause,[],[f681])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    v1_relat_1(sK4) | ~spl8_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f590,plain,(
% 0.21/0.49    spl8_57 | ~spl8_17 | ~spl8_56),
% 0.21/0.49    inference(avatar_split_clause,[],[f585,f580,f197,f587])).
% 0.21/0.49  fof(f580,plain,(
% 0.21/0.49    spl8_56 <=> v5_relat_1(sK4,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 0.21/0.49  fof(f585,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK4),sK3) | (~spl8_17 | ~spl8_56)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f199,f582,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f582,plain,(
% 0.21/0.49    v5_relat_1(sK4,sK3) | ~spl8_56),
% 0.21/0.49    inference(avatar_component_clause,[],[f580])).
% 0.21/0.49  fof(f584,plain,(
% 0.21/0.49    spl8_56 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f576,f88,f580])).
% 0.21/0.49  fof(f576,plain,(
% 0.21/0.49    v5_relat_1(sK4,sK3) | ~spl8_2),
% 0.21/0.49    inference(resolution,[],[f80,f90])).
% 0.21/0.49  % (6003)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (6003)Refutation not found, incomplete strategy% (6003)------------------------------
% 0.21/0.49  % (6003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6003)Memory used [KB]: 6140
% 0.21/0.49  % (6003)Time elapsed: 0.092 s
% 0.21/0.49  % (6003)------------------------------
% 0.21/0.49  % (6003)------------------------------
% 0.21/0.49  % (6007)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (6023)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (6012)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (6004)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6021)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (6015)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6004)Refutation not found, incomplete strategy% (6004)------------------------------
% 0.21/0.50  % (6004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6004)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6004)Memory used [KB]: 10618
% 0.21/0.50  % (6004)Time elapsed: 0.093 s
% 0.21/0.50  % (6004)------------------------------
% 0.21/0.50  % (6004)------------------------------
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    ~spl8_40 | spl8_37),
% 0.21/0.50    inference(avatar_split_clause,[],[f409,f402,f421])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    spl8_37 <=> r2_hidden(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) | spl8_37),
% 0.21/0.50    inference(resolution,[],[f404,f220])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X2,X3] : (r2_hidden(X3,k1_zfmisc_1(X2)) | ~r1_tarski(X3,X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f210,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ( ! [X2,X3] : (v1_xboole_0(k1_zfmisc_1(X2)) | r2_hidden(X3,k1_zfmisc_1(X2)) | ~r1_tarski(X3,X2)) )),
% 0.21/0.50    inference(resolution,[],[f65,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    ~r2_hidden(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) | spl8_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f402])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    ~spl8_37 | ~spl8_8 | spl8_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f397,f346,f121,f402])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl8_8 <=> r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    spl8_31 <=> sP0(k1_zfmisc_1(sK3),sK5(k2_relset_1(sK2,sK3,sK4)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    ~r2_hidden(k2_relset_1(sK2,sK3,sK4),k1_zfmisc_1(sK3)) | (~spl8_8 | spl8_31)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f123,f348,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP0(X0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & ((r2_hidden(sK7(X0,X1),X0) & r2_hidden(X1,sK7(X0,X1))) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) => (r2_hidden(sK7(X0,X1),X0) & r2_hidden(X1,sK7(X0,X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X2] : ((sP0(X0,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~sP0(X0,X2)))),
% 0.21/0.50    inference(nnf_transformation,[],[f29])).
% 0.21/0.50  % (6022)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X2] : (sP0(X0,X2) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    ~sP0(k1_zfmisc_1(sK3),sK5(k2_relset_1(sK2,sK3,sK4))) | spl8_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f346])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) | ~spl8_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    ~spl8_31 | spl8_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f341,f128,f346])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl8_9 <=> r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ~sP0(k1_zfmisc_1(sK3),sK5(k2_relset_1(sK2,sK3,sK4))) | spl8_9),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f130,f102,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~sP0(X0,X3) | r2_hidden(X3,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(X0,sK6(X0,X1)) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(X0,sK6(X0,X1)) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1))) => ((~sP0(X0,sK6(X0,X1)) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(X0,sK6(X0,X1)) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X0,X2)) & (sP0(X0,X2) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X0,X2)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ( ! [X0] : (sP1(k1_zfmisc_1(X0),X0)) )),
% 0.21/0.50    inference(superposition,[],[f81,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (sP1(X0,k3_tarski(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP1(X0,X1) | k3_tarski(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k3_tarski(X0) != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP1(X0,X1))),
% 0.21/0.50    inference(definition_folding,[],[f2,f30,f29])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),sK3) | spl8_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f128])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl8_17 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f201,f88,f197])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    v1_relat_1(sK4) | ~spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f193,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK3)) | ~spl8_2),
% 0.21/0.50    inference(resolution,[],[f59,f90])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ~spl8_9 | spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f126,f111,f128])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl8_6 <=> m1_subset_1(sK5(k2_relset_1(sK2,sK3,sK4)),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ~r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),sK3) | spl8_6),
% 0.21/0.50    inference(resolution,[],[f113,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ~m1_subset_1(sK5(k2_relset_1(sK2,sK3,sK4)),sK3) | spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f111])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl8_8 | spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f119,f115,f121])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl8_7 <=> k1_xboole_0 = k2_relset_1(sK2,sK3,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    r2_hidden(sK5(k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) | spl8_7),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f116,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relset_1(sK2,sK3,sK4) | spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~spl8_6 | spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f115,f111])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relset_1(sK2,sK3,sK4) | ~m1_subset_1(sK5(k2_relset_1(sK2,sK3,sK4)),sK3)),
% 0.21/0.50    inference(resolution,[],[f60,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,sK4)) | ~m1_subset_1(X3,sK3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,sK4)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f34,f33,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK2,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK2,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,X2)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k1_relset_1(sK2,sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,X2)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k1_relset_1(sK2,sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,sK4)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f88])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl8_1 <=> k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(sK2,sK3,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (6019)------------------------------
% 0.21/0.50  % (6019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6019)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (6019)Memory used [KB]: 11257
% 0.21/0.50  % (6019)Time elapsed: 0.088 s
% 0.21/0.50  % (6019)------------------------------
% 0.21/0.50  % (6019)------------------------------
% 0.21/0.50  % (6020)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (6000)Success in time 0.153 s
%------------------------------------------------------------------------------
