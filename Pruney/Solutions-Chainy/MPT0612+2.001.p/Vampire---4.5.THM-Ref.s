%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 121 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  191 ( 308 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f42,f47,f51,f55,f60,f65,f85,f114,f124,f130,f135,f138])).

fof(f138,plain,
    ( ~ spl3_2
    | spl3_4
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl3_2
    | spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f46,plain,
    ( k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_4
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f136,plain,
    ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(resolution,[],[f134,f37])).

fof(f37,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f135,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f131,f128,f53,f133])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0))
        | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(resolution,[],[f129,f54])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0))
        | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl3_20
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f126,f122,f83,f63,f128])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f122,plain,
    ( spl3_19
  <=> ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0))
        | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) )
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f125,f64])).

fof(f64,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0))
        | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)
        | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) )
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(superposition,[],[f84,f123])).

fof(f123,plain,
    ( ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k1_relat_1(X0))
        | k7_relat_1(X0,X1) = k1_xboole_0
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f124,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f115,f112,f30,f122])).

fof(f30,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f112,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f115,plain,
    ( ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(resolution,[],[f113,f32])).

fof(f32,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f28,f112])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f24,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f85,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f21,f83])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f65,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f61,f58,f40,f63])).

fof(f40,plain,
    ( spl3_3
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f61,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f56,f49,f30,f58])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | v1_relat_1(X0) )
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f47,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f19,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f40])).

fof(f27,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.41  % (2113)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.42  % (2113)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f139,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f33,f38,f42,f47,f51,f55,f60,f65,f85,f114,f124,f130,f135,f138])).
% 0.22/0.42  fof(f138,plain,(
% 0.22/0.42    ~spl3_2 | spl3_4 | ~spl3_21),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f137])).
% 0.22/0.42  fof(f137,plain,(
% 0.22/0.42    $false | (~spl3_2 | spl3_4 | ~spl3_21)),
% 0.22/0.42    inference(subsumption_resolution,[],[f136,f46])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f44])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl3_4 <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f136,plain,(
% 0.22/0.42    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | (~spl3_2 | ~spl3_21)),
% 0.22/0.42    inference(resolution,[],[f134,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.42  fof(f134,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)) ) | ~spl3_21),
% 0.22/0.42    inference(avatar_component_clause,[],[f133])).
% 0.22/0.42  fof(f133,plain,(
% 0.22/0.42    spl3_21 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) | ~r1_tarski(X1,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.42  fof(f135,plain,(
% 0.22/0.42    spl3_21 | ~spl3_6 | ~spl3_20),
% 0.22/0.42    inference(avatar_split_clause,[],[f131,f128,f53,f133])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl3_6 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.42  fof(f128,plain,(
% 0.22/0.42    spl3_20 <=> ! [X1,X0] : (~r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0)) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.42  fof(f131,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) | ~r1_tarski(X1,X0)) ) | (~spl3_6 | ~spl3_20)),
% 0.22/0.42    inference(resolution,[],[f129,f54])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f53])).
% 0.22/0.42  fof(f129,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0)) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)) ) | ~spl3_20),
% 0.22/0.42    inference(avatar_component_clause,[],[f128])).
% 0.22/0.42  fof(f130,plain,(
% 0.22/0.42    spl3_20 | ~spl3_8 | ~spl3_12 | ~spl3_19),
% 0.22/0.42    inference(avatar_split_clause,[],[f126,f122,f83,f63,f128])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    spl3_8 <=> ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.42  fof(f83,plain,(
% 0.22/0.42    spl3_12 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.42  fof(f122,plain,(
% 0.22/0.42    spl3_19 <=> ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.42  fof(f126,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0)) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)) ) | (~spl3_8 | ~spl3_12 | ~spl3_19)),
% 0.22/0.42    inference(subsumption_resolution,[],[f125,f64])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK2,X0))) ) | ~spl3_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f63])).
% 0.22/0.42  fof(f125,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k4_xboole_0(k1_relat_1(sK2),X0)) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) | ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)))) ) | (~spl3_12 | ~spl3_19)),
% 0.22/0.42    inference(superposition,[],[f84,f123])).
% 0.22/0.42  fof(f123,plain,(
% 0.22/0.42    ( ! [X0] : (k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)) ) | ~spl3_19),
% 0.22/0.42    inference(avatar_component_clause,[],[f122])).
% 0.22/0.42  fof(f84,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k7_relat_1(X0,X1) = k1_xboole_0 | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f83])).
% 0.22/0.42  fof(f124,plain,(
% 0.22/0.42    spl3_19 | ~spl3_1 | ~spl3_18),
% 0.22/0.42    inference(avatar_split_clause,[],[f115,f112,f30,f122])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f112,plain,(
% 0.22/0.42    spl3_18 <=> ! [X1,X0] : (k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.42  fof(f115,plain,(
% 0.22/0.42    ( ! [X0] : (k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)) ) | (~spl3_1 | ~spl3_18)),
% 0.22/0.42    inference(resolution,[],[f113,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f30])).
% 0.22/0.42  fof(f113,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)) ) | ~spl3_18),
% 0.22/0.42    inference(avatar_component_clause,[],[f112])).
% 0.22/0.42  fof(f114,plain,(
% 0.22/0.42    spl3_18),
% 0.22/0.42    inference(avatar_split_clause,[],[f28,f112])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f24,f23,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.22/0.42  fof(f85,plain,(
% 0.22/0.42    spl3_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f21,f83])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    spl3_8 | ~spl3_3 | ~spl3_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f61,f58,f40,f63])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl3_3 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    spl3_7 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK2,X0))) ) | (~spl3_3 | ~spl3_7)),
% 0.22/0.42    inference(resolution,[],[f59,f41])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl3_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f40])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_relat_1(X0)) ) | ~spl3_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f58])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    spl3_7 | ~spl3_1 | ~spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f56,f49,f30,f58])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    spl3_5 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_relat_1(X0)) ) | (~spl3_1 | ~spl3_5)),
% 0.22/0.42    inference(resolution,[],[f50,f32])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) ) | ~spl3_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f49])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl3_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f25,f53])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f49])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ~spl3_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f26,f44])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.42    inference(definition_unfolding,[],[f19,f23])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.42    inference(flattening,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.22/0.42    inference(negated_conjecture,[],[f7])).
% 0.22/0.42  fof(f7,conjecture,(
% 0.22/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    spl3_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f27,f40])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.42    inference(definition_unfolding,[],[f22,f23])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    spl3_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f35])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    r1_tarski(sK0,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl3_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    v1_relat_1(sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (2113)------------------------------
% 0.22/0.42  % (2113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (2113)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (2113)Memory used [KB]: 6140
% 0.22/0.42  % (2113)Time elapsed: 0.008 s
% 0.22/0.42  % (2113)------------------------------
% 0.22/0.42  % (2113)------------------------------
% 0.22/0.42  % (2105)Success in time 0.06 s
%------------------------------------------------------------------------------
