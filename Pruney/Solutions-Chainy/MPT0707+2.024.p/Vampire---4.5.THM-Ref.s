%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 115 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  181 ( 263 expanded)
%              Number of equality atoms :   48 (  73 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f53,f57,f61,f65,f69,f75,f81,f93,f98,f106,f114])).

fof(f114,plain,
    ( spl2_1
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl2_1
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f112,f89])).

fof(f89,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_13
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f112,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_1
    | ~ spl2_15 ),
    inference(superposition,[],[f31,f105])).

fof(f105,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_15
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f31,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f106,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f102,f96,f59,f43,f39,f104])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f96,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f102,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f101,f44])).

fof(f44,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f101,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f100,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f100,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f99,f44])).

fof(f99,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f97,f40])).

fof(f40,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f94,f51,f39,f96])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f93,plain,
    ( spl2_13
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f85,f78,f55,f87])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

% (6732)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f78,plain,
    ( spl2_12
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f85,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(superposition,[],[f56,f80])).

fof(f80,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f56,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f81,plain,
    ( spl2_12
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f76,f72,f63,f78])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f72,plain,
    ( spl2_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f76,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(resolution,[],[f64,f74])).

fof(f74,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f75,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f70,f67,f34,f72])).

fof(f34,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f67,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f70,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f68,f36])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:39:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (6736)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.42  % (6726)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.42  % (6736)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f115,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f53,f57,f61,f65,f69,f75,f81,f93,f98,f106,f114])).
% 0.22/0.42  fof(f114,plain,(
% 0.22/0.42    spl2_1 | ~spl2_13 | ~spl2_15),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f113])).
% 0.22/0.42  fof(f113,plain,(
% 0.22/0.42    $false | (spl2_1 | ~spl2_13 | ~spl2_15)),
% 0.22/0.42    inference(subsumption_resolution,[],[f112,f89])).
% 0.22/0.42  fof(f89,plain,(
% 0.22/0.42    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_13),
% 0.22/0.42    inference(avatar_component_clause,[],[f87])).
% 0.22/0.42  fof(f87,plain,(
% 0.22/0.42    spl2_13 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.42  fof(f112,plain,(
% 0.22/0.42    sK1 != k3_xboole_0(sK0,sK1) | (spl2_1 | ~spl2_15)),
% 0.22/0.42    inference(superposition,[],[f31,f105])).
% 0.22/0.42  fof(f105,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f104])).
% 0.22/0.42  fof(f104,plain,(
% 0.22/0.42    spl2_15 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f106,plain,(
% 0.22/0.42    spl2_15 | ~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_14),
% 0.22/0.42    inference(avatar_split_clause,[],[f102,f96,f59,f43,f39,f104])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl2_8 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.42  fof(f96,plain,(
% 0.22/0.42    spl2_14 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_14)),
% 0.22/0.42    inference(forward_demodulation,[],[f101,f44])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f43])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) ) | (~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_14)),
% 0.22/0.42    inference(forward_demodulation,[],[f100,f60])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f59])).
% 0.22/0.42  fof(f100,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_4 | ~spl2_14)),
% 0.22/0.42    inference(forward_demodulation,[],[f99,f44])).
% 0.22/0.42  fof(f99,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) ) | (~spl2_3 | ~spl2_14)),
% 0.22/0.42    inference(resolution,[],[f97,f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f39])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0))) ) | ~spl2_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f96])).
% 0.22/0.42  fof(f98,plain,(
% 0.22/0.42    spl2_14 | ~spl2_3 | ~spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f94,f51,f39,f96])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl2_6 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.42  fof(f94,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_6)),
% 0.22/0.42    inference(resolution,[],[f52,f40])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f51])).
% 0.22/0.42  fof(f93,plain,(
% 0.22/0.42    spl2_13 | ~spl2_7 | ~spl2_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f85,f78,f55,f87])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.42  % (6732)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  fof(f78,plain,(
% 0.22/0.42    spl2_12 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.42  fof(f85,plain,(
% 0.22/0.42    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_7 | ~spl2_12)),
% 0.22/0.42    inference(superposition,[],[f56,f80])).
% 0.22/0.42  fof(f80,plain,(
% 0.22/0.42    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f78])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f55])).
% 0.22/0.42  fof(f81,plain,(
% 0.22/0.42    spl2_12 | ~spl2_9 | ~spl2_11),
% 0.22/0.42    inference(avatar_split_clause,[],[f76,f72,f63,f78])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    spl2_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    spl2_11 <=> r1_tarski(sK1,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_9 | ~spl2_11)),
% 0.22/0.42    inference(resolution,[],[f64,f74])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    r1_tarski(sK1,sK0) | ~spl2_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f72])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f63])).
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    spl2_11 | ~spl2_2 | ~spl2_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f70,f67,f34,f72])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl2_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_10)),
% 0.22/0.42    inference(resolution,[],[f68,f36])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f34])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f67])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl2_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f27,f67])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.42    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    spl2_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f26,f63])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    spl2_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f25,f59])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,axiom,(
% 0.22/0.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl2_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f55])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f51])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    spl2_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f22,f43])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    spl2_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f39])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.42    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    spl2_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f34])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.42    inference(negated_conjecture,[],[f8])).
% 0.22/0.42  fof(f8,conjecture,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ~spl2_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f29])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (6736)------------------------------
% 0.22/0.42  % (6736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (6736)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (6736)Memory used [KB]: 6140
% 0.22/0.42  % (6736)Time elapsed: 0.006 s
% 0.22/0.42  % (6736)------------------------------
% 0.22/0.42  % (6736)------------------------------
% 0.22/0.43  % (6725)Success in time 0.06 s
%------------------------------------------------------------------------------
