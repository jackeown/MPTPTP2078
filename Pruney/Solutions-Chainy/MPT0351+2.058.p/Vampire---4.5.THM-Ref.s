%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 171 expanded)
%              Number of leaves         :   37 (  81 expanded)
%              Depth                    :    6
%              Number of atoms          :  279 ( 389 expanded)
%              Number of equality atoms :   65 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17318)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f559,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f75,f79,f87,f91,f95,f99,f107,f119,f131,f139,f164,f172,f176,f227,f247,f276,f282,f383,f388,f507,f546])).

fof(f546,plain,
    ( spl2_34
    | ~ spl2_42
    | ~ spl2_43
    | ~ spl2_47 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl2_34
    | ~ spl2_42
    | ~ spl2_43
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f275,f544])).

fof(f544,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl2_42
    | ~ spl2_43
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f524,f382])).

fof(f382,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl2_42
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f524,plain,
    ( k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0))
    | ~ spl2_43
    | ~ spl2_47 ),
    inference(superposition,[],[f506,f387])).

fof(f387,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl2_43
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f506,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f505])).

fof(f505,plain,
    ( spl2_47
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f275,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | spl2_34 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl2_34
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f507,plain,
    ( spl2_47
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f189,f170,f105,f505])).

fof(f105,plain,
    ( spl2_11
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f170,plain,
    ( spl2_22
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f189,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(superposition,[],[f171,f106])).

fof(f106,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f171,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f388,plain,
    ( spl2_43
    | ~ spl2_19
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f283,f244,f137,f385])).

fof(f137,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f244,plain,
    ( spl2_29
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f283,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_19
    | ~ spl2_29 ),
    inference(unit_resulting_resolution,[],[f246,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f137])).

fof(f246,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f244])).

fof(f383,plain,
    ( spl2_42
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f213,f174,f105,f97,f89,f381])).

fof(f89,plain,
    ( spl2_7
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f97,plain,
    ( spl2_9
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f174,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f213,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f196,f140])).

fof(f140,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(superposition,[],[f106,f98])).

fof(f98,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f196,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_7
    | ~ spl2_23 ),
    inference(superposition,[],[f175,f90])).

fof(f90,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f89])).

% (17312)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f175,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f174])).

fof(f282,plain,
    ( ~ spl2_6
    | spl2_33 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl2_6
    | spl2_33 ),
    inference(unit_resulting_resolution,[],[f86,f271])).

fof(f271,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl2_33 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl2_33
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f86,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_6
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f276,plain,
    ( ~ spl2_1
    | ~ spl2_33
    | ~ spl2_34
    | spl2_3
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f236,f225,f72,f273,f269,f61])).

fof(f61,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f72,plain,
    ( spl2_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f225,plain,
    ( spl2_26
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f236,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl2_3
    | ~ spl2_26 ),
    inference(superposition,[],[f74,f226])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f225])).

fof(f74,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f247,plain,
    ( spl2_29
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f219,f161,f117,f93,f244])).

fof(f93,plain,
    ( spl2_8
  <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f117,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f161,plain,
    ( spl2_20
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f219,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f217,f94])).

fof(f94,plain,
    ( ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f217,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f163,f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f163,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f227,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f54,f225])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f176,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f53,f174])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f172,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f45,f170])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f164,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f151,f129,f77,f61,f161])).

fof(f77,plain,
    ( spl2_4
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f129,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f151,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f78,f63,f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f78,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f139,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f51,f137])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f131,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f46,f129])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f119,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f50,f117])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f107,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f42,f105])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f99,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f39,f97])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f95,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f91,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f87,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f59,f85])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f40,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f79,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f75,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f70,f66,f72])).

fof(f66,plain,
    ( spl2_2
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f70,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl2_2 ),
    inference(forward_demodulation,[],[f68,f36])).

fof(f68,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f64,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (17317)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (17317)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (17325)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.47  % (17318)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  fof(f559,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f64,f69,f75,f79,f87,f91,f95,f99,f107,f119,f131,f139,f164,f172,f176,f227,f247,f276,f282,f383,f388,f507,f546])).
% 0.20/0.47  fof(f546,plain,(
% 0.20/0.47    spl2_34 | ~spl2_42 | ~spl2_43 | ~spl2_47),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f545])).
% 0.20/0.47  fof(f545,plain,(
% 0.20/0.47    $false | (spl2_34 | ~spl2_42 | ~spl2_43 | ~spl2_47)),
% 0.20/0.47    inference(subsumption_resolution,[],[f275,f544])).
% 0.20/0.47  fof(f544,plain,(
% 0.20/0.47    sK0 = k2_xboole_0(sK1,sK0) | (~spl2_42 | ~spl2_43 | ~spl2_47)),
% 0.20/0.47    inference(forward_demodulation,[],[f524,f382])).
% 0.20/0.47  fof(f382,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_42),
% 0.20/0.47    inference(avatar_component_clause,[],[f381])).
% 0.20/0.47  fof(f381,plain,(
% 0.20/0.47    spl2_42 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.20/0.47  fof(f524,plain,(
% 0.20/0.47    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0)) | (~spl2_43 | ~spl2_47)),
% 0.20/0.47    inference(superposition,[],[f506,f387])).
% 0.20/0.47  fof(f387,plain,(
% 0.20/0.47    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_43),
% 0.20/0.47    inference(avatar_component_clause,[],[f385])).
% 0.20/0.47  fof(f385,plain,(
% 0.20/0.47    spl2_43 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.47  fof(f506,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | ~spl2_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f505])).
% 0.20/0.47  fof(f505,plain,(
% 0.20/0.47    spl2_47 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.20/0.47  fof(f275,plain,(
% 0.20/0.47    sK0 != k2_xboole_0(sK1,sK0) | spl2_34),
% 0.20/0.47    inference(avatar_component_clause,[],[f273])).
% 0.20/0.47  fof(f273,plain,(
% 0.20/0.47    spl2_34 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.47  fof(f507,plain,(
% 0.20/0.47    spl2_47 | ~spl2_11 | ~spl2_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f189,f170,f105,f505])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl2_11 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    spl2_22 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | (~spl2_11 | ~spl2_22)),
% 0.20/0.47    inference(superposition,[],[f171,f106])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f170])).
% 0.20/0.47  fof(f388,plain,(
% 0.20/0.47    spl2_43 | ~spl2_19 | ~spl2_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f283,f244,f137,f385])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    spl2_19 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    spl2_29 <=> r1_tarski(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_19 | ~spl2_29)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f246,f138])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f137])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    r1_tarski(sK1,sK0) | ~spl2_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f244])).
% 0.20/0.47  fof(f383,plain,(
% 0.20/0.47    spl2_42 | ~spl2_7 | ~spl2_9 | ~spl2_11 | ~spl2_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f213,f174,f105,f97,f89,f381])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl2_7 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl2_9 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    spl2_23 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_7 | ~spl2_9 | ~spl2_11 | ~spl2_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f196,f140])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl2_9 | ~spl2_11)),
% 0.20/0.47    inference(superposition,[],[f106,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_7 | ~spl2_23)),
% 0.20/0.47    inference(superposition,[],[f175,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  % (17312)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f174])).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    ~spl2_6 | spl2_33),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f277])).
% 0.20/0.47  fof(f277,plain,(
% 0.20/0.47    $false | (~spl2_6 | spl2_33)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f86,f271])).
% 0.20/0.47  fof(f271,plain,(
% 0.20/0.47    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl2_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f269])).
% 0.20/0.47  fof(f269,plain,(
% 0.20/0.47    spl2_33 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl2_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl2_6 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    ~spl2_1 | ~spl2_33 | ~spl2_34 | spl2_3 | ~spl2_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f236,f225,f72,f273,f269,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl2_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    spl2_26 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.47  fof(f236,plain,(
% 0.20/0.47    sK0 != k2_xboole_0(sK1,sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl2_3 | ~spl2_26)),
% 0.20/0.47    inference(superposition,[],[f74,f226])).
% 0.20/0.47  fof(f226,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f225])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    sK0 != k4_subset_1(sK0,sK1,sK0) | spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    spl2_29 | ~spl2_8 | ~spl2_14 | ~spl2_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f219,f161,f117,f93,f244])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl2_8 <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl2_14 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl2_20 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    r1_tarski(sK1,sK0) | (~spl2_8 | ~spl2_14 | ~spl2_20)),
% 0.20/0.47    inference(forward_demodulation,[],[f217,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) ) | ~spl2_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) | (~spl2_14 | ~spl2_20)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f163,f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) ) | ~spl2_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f117])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl2_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f161])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    spl2_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f225])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl2_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f53,f174])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    spl2_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f170])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl2_20 | ~spl2_1 | ~spl2_4 | ~spl2_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f151,f129,f77,f61,f161])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl2_4 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    spl2_17 <=> ! [X1,X0] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_zfmisc_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_17)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f78,f63,f130])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f129])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f61])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl2_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f77])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    spl2_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f137])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    spl2_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f129])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(nnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl2_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f50,f117])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl2_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f105])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl2_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f97])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl2_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f93])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl2_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f89])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f59,f85])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f40,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,axiom,(
% 0.20/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,axiom,(
% 0.20/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl2_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f77])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,axiom,(
% 0.20/0.47    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ~spl2_3 | spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f70,f66,f72])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl2_2 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    sK0 != k4_subset_1(sK0,sK1,sK0) | spl2_2),
% 0.20/0.47    inference(forward_demodulation,[],[f68,f36])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) | spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f66])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f22])).
% 0.20/0.47  fof(f22,conjecture,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f61])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (17314)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (17313)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (17317)------------------------------
% 0.20/0.48  % (17317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17317)Termination reason: Refutation
% 0.20/0.48  % (17322)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (17319)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (17320)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (17327)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  
% 0.20/0.48  % (17317)Memory used [KB]: 6524
% 0.20/0.48  % (17317)Time elapsed: 0.067 s
% 0.20/0.48  % (17317)------------------------------
% 0.20/0.48  % (17317)------------------------------
% 0.20/0.49  % (17311)Success in time 0.124 s
%------------------------------------------------------------------------------
