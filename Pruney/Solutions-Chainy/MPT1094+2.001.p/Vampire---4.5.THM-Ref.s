%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 128 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  210 ( 411 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f469,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f53,f58,f63,f97,f106,f129,f292,f467])).

fof(f467,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f457,f60,f55,f49,f45])).

fof(f45,plain,
    ( spl1_1
  <=> v1_finset_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f49,plain,
    ( spl1_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f55,plain,
    ( spl1_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f60,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f457,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f50,f98,f40,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v1_finset_1(k1_relat_1(X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f40,plain,(
    ! [X0,X1] : v1_funct_1(k9_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0)))
      & v1_funct_1(k9_funct_3(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0)))
      & v1_funct_2(k9_funct_3(X0,X1),k2_zfmisc_1(X0,X1),X0)
      & v1_funct_1(k9_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_funct_3)).

fof(f98,plain,(
    ! [X0,X1] : v1_relat_1(k9_funct_3(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f42,f41,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f50,plain,
    ( v1_finset_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f62,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f292,plain,
    ( ~ spl1_13
    | spl1_2
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f291,f103,f49,f126])).

fof(f126,plain,
    ( spl1_13
  <=> v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f103,plain,
    ( spl1_10
  <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f291,plain,
    ( v1_finset_1(sK0)
    | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_10 ),
    inference(superposition,[],[f36,f105])).

fof(f105,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).

fof(f129,plain,
    ( spl1_13
    | ~ spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f117,f94,f45,f126])).

fof(f94,plain,
    ( spl1_9
  <=> v1_finset_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f117,plain,
    ( v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_1
    | ~ spl1_9 ),
    inference(unit_resulting_resolution,[],[f46,f96,f34])).

% (30812)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).

fof(f96,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f46,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f106,plain,
    ( spl1_10
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f99,f60,f103])).

fof(f99,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f97,plain,
    ( spl1_9
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f92,f60,f55,f45,f94])).

fof(f92,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f46,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).

fof(f63,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ v1_finset_1(sK0)
      | ~ v1_finset_1(k1_relat_1(sK0)) )
    & ( v1_finset_1(sK0)
      | v1_finset_1(k1_relat_1(sK0)) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(X0)
          | ~ v1_finset_1(k1_relat_1(X0)) )
        & ( v1_finset_1(X0)
          | v1_finset_1(k1_relat_1(X0)) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v1_finset_1(sK0)
        | ~ v1_finset_1(k1_relat_1(sK0)) )
      & ( v1_finset_1(sK0)
        | v1_finset_1(k1_relat_1(sK0)) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
        <=> v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
      <=> v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).

fof(f58,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f32,f49,f45])).

fof(f32,plain,
    ( v1_finset_1(sK0)
    | v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f33,f49,f45])).

fof(f33,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:35:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (30818)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.54  % (30818)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (30829)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.54  % (30821)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f469,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f52,f53,f58,f63,f97,f106,f129,f292,f467])).
% 0.21/0.55  fof(f467,plain,(
% 0.21/0.55    spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f457,f60,f55,f49,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    spl1_1 <=> v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    spl1_2 <=> v1_finset_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    spl1_3 <=> v1_funct_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    spl1_4 <=> v1_relat_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.55  fof(f457,plain,(
% 0.21/0.55    v1_finset_1(k1_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f62,f57,f50,f98,f40,f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X0] : (v1_finset_1(k1_relat_1(X0)) | ~v1_finset_1(X0) | ~v1_funct_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(superposition,[],[f35,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | (~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_finset_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => v1_finset_1(k9_relat_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_funct_1(k9_funct_3(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0))) & v1_funct_1(k9_funct_3(X0,X1)))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0))) & v1_funct_2(k9_funct_3(X0,X1),k2_zfmisc_1(X0,X1),X0) & v1_funct_1(k9_funct_3(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_funct_3)).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k9_funct_3(X0,X1))) )),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f42,f41,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    v1_finset_1(sK0) | ~spl1_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f49])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    v1_funct_1(sK0) | ~spl1_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f55])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f60])).
% 0.21/0.55  fof(f292,plain,(
% 0.21/0.55    ~spl1_13 | spl1_2 | ~spl1_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f291,f103,f49,f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl1_13 <=> v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    spl1_10 <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    v1_finset_1(sK0) | ~v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_10),
% 0.21/0.55    inference(superposition,[],[f36,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f103])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_finset_1(X1) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    spl1_13 | ~spl1_1 | ~spl1_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f117,f94,f45,f126])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl1_9 <=> v1_finset_1(k2_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | (~spl1_1 | ~spl1_9)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f46,f96,f34])).
% 0.21/0.55  % (30812)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0))),
% 0.21/0.55    inference(flattening,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | (~v1_finset_1(X1) | ~v1_finset_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_finset_1(X1) & v1_finset_1(X0)) => v1_finset_1(k2_zfmisc_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    v1_finset_1(k2_relat_1(sK0)) | ~spl1_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f94])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    v1_finset_1(k1_relat_1(sK0)) | ~spl1_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f45])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl1_10 | ~spl1_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f99,f60,f103])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_4),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f62,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    spl1_9 | ~spl1_1 | ~spl1_3 | ~spl1_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f92,f60,f55,f45,f94])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    v1_finset_1(k2_relat_1(sK0)) | (~spl1_1 | ~spl1_3 | ~spl1_4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f62,f57,f46,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0] : (v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : ((v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) => v1_finset_1(k2_relat_1(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    spl1_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f30,f60])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    v1_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    (~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))) & (v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ? [X0] : ((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))) & (v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ? [X0] : ((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ? [X0] : (((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0)))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : ((v1_finset_1(k1_relat_1(X0)) <~> v1_finset_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0] : ((v1_finset_1(k1_relat_1(X0)) <~> v1_finset_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) <=> v1_finset_1(X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f10])).
% 0.21/0.55  fof(f10,conjecture,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) <=> v1_finset_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    spl1_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f31,f55])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    v1_funct_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    spl1_1 | spl1_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f32,f49,f45])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ~spl1_1 | ~spl1_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f33,f49,f45])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (30818)------------------------------
% 0.21/0.55  % (30818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30818)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (30818)Memory used [KB]: 11001
% 0.21/0.55  % (30818)Time elapsed: 0.116 s
% 0.21/0.55  % (30818)------------------------------
% 0.21/0.55  % (30818)------------------------------
% 0.21/0.55  % (30831)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.55  % (30808)Success in time 0.182 s
%------------------------------------------------------------------------------
