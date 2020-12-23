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
% DateTime   : Thu Dec  3 12:54:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 111 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :  184 ( 270 expanded)
%              Number of equality atoms :   46 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f40,f44,f52,f56,f60,f68,f75,f80,f85,f92,f98,f102])).

fof(f102,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f100,f30])).

fof(f30,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f100,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f99,f43])).

fof(f43,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f99,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(superposition,[],[f84,f97])).

fof(f97,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_15
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f84,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_13
  <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f98,plain,
    ( spl2_15
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f93,f90,f72,f95])).

fof(f72,plain,
    ( spl2_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f90,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f93,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(resolution,[],[f91,f74])).

fof(f74,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f88,f78,f58,f42,f38,f90])).

fof(f38,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f58,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f78,plain,
    ( spl2_12
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f87,f79])).

fof(f79,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f86,f43])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f85,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f81,f54,f38,f83])).

fof(f54,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f81,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f55,f39])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f80,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f76,f50,f38,f78])).

fof(f50,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f76,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f75,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f69,f66,f33,f72])).

fof(f33,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f69,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f67,f35])).

fof(f35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f56,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f52,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f44,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f28])).

fof(f18,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (21883)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (21886)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (21883)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f31,f36,f40,f44,f52,f56,f60,f68,f75,f80,f85,f92,f98,f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl2_1 | ~spl2_4 | ~spl2_13 | ~spl2_15),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    $false | (spl2_1 | ~spl2_4 | ~spl2_13 | ~spl2_15)),
% 0.21/0.42    inference(subsumption_resolution,[],[f100,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | (~spl2_4 | ~spl2_13 | ~spl2_15)),
% 0.21/0.42    inference(forward_demodulation,[],[f99,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) | (~spl2_13 | ~spl2_15)),
% 0.21/0.42    inference(superposition,[],[f84,f97])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl2_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f95])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    spl2_15 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f83])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl2_13 <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    spl2_15 | ~spl2_11 | ~spl2_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f93,f90,f72,f95])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl2_11 <=> r1_tarski(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl2_14 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_11 | ~spl2_14)),
% 0.21/0.42    inference(resolution,[],[f91,f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f72])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f90])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    spl2_14 | ~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f88,f78,f58,f42,f38,f90])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_8 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl2_12 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_12)),
% 0.21/0.42    inference(forward_demodulation,[],[f87,f79])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f78])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_3 | ~spl2_4 | ~spl2_8)),
% 0.21/0.42    inference(forward_demodulation,[],[f86,f43])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_3 | ~spl2_8)),
% 0.21/0.42    inference(resolution,[],[f59,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl2_13 | ~spl2_3 | ~spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f81,f54,f38,f83])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_3 | ~spl2_7)),
% 0.21/0.42    inference(resolution,[],[f55,f39])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f54])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl2_12 | ~spl2_3 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f76,f50,f38,f78])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_6)),
% 0.21/0.42    inference(resolution,[],[f51,f39])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    spl2_11 | ~spl2_2 | ~spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f69,f66,f33,f72])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl2_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_10)),
% 0.21/0.42    inference(resolution,[],[f67,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f66])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f54])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f42])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f38])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f33])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f28])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (21883)------------------------------
% 0.21/0.42  % (21883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (21883)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (21883)Memory used [KB]: 10618
% 0.21/0.42  % (21883)Time elapsed: 0.007 s
% 0.21/0.42  % (21883)------------------------------
% 0.21/0.42  % (21883)------------------------------
% 0.21/0.42  % (21877)Success in time 0.065 s
%------------------------------------------------------------------------------
