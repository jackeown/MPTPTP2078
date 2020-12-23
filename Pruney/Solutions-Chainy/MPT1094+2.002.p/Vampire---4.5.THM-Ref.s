%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 194 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  215 ( 733 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f59,f95,f102,f107,f111])).

fof(f111,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | spl1_4 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_3
    | spl1_4 ),
    inference(subsumption_resolution,[],[f109,f53])).

fof(f53,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_1
  <=> v1_finset_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f109,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ spl1_3
    | spl1_4 ),
    inference(subsumption_resolution,[],[f108,f101])).

fof(f101,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl1_3
  <=> v1_finset_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f108,plain,
    ( ~ v1_finset_1(k2_relat_1(sK0))
    | ~ v1_finset_1(k1_relat_1(sK0))
    | spl1_4 ),
    inference(resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).

fof(f106,plain,
    ( ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl1_4
  <=> v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f107,plain,
    ( ~ spl1_4
    | spl1_2 ),
    inference(avatar_split_clause,[],[f66,f55,f104])).

fof(f55,plain,
    ( spl1_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f66,plain,
    ( v1_finset_1(sK0)
    | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(superposition,[],[f44,f63])).

fof(f63,plain,(
    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ v1_finset_1(sK0)
      | ~ v1_finset_1(k1_relat_1(sK0)) )
    & ( v1_finset_1(sK0)
      | v1_finset_1(k1_relat_1(sK0)) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f30,plain,
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

fof(f29,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
        <=> v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
      <=> v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).

fof(f102,plain,
    ( ~ spl1_1
    | spl1_3 ),
    inference(avatar_split_clause,[],[f79,f99,f51])).

fof(f79,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(superposition,[],[f78,f60])).

fof(f60,plain,(
    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(resolution,[],[f36,f32])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f78,plain,(
    ! [X0] :
      ( v1_finset_1(k9_relat_1(sK0,X0))
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f77,f70])).

fof(f70,plain,(
    ! [X1] :
      ( v1_finset_1(k1_relat_1(k7_relat_1(sK0,X1)))
      | ~ v1_finset_1(X1) ) ),
    inference(superposition,[],[f44,f67])).

fof(f67,plain,(
    ! [X0] : k3_xboole_0(k1_relat_1(sK0),X0) = k1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k1_relat_1(k7_relat_1(sK0,X0)))
      | v1_finset_1(k9_relat_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f76,f32])).

fof(f76,plain,(
    ! [X0] :
      ( v1_finset_1(k9_relat_1(sK0,X0))
      | ~ v1_finset_1(k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0] :
      ( v1_finset_1(k9_relat_1(sK0,X0))
      | ~ v1_finset_1(k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f46,f73])).

fof(f73,plain,(
    ! [X0] : k9_relat_1(sK0,X0) = k9_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(forward_demodulation,[],[f71,f67])).

fof(f71,plain,(
    ! [X0] : k9_relat_1(sK0,X0) = k9_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0)) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f95,plain,
    ( spl1_1
    | ~ spl1_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k9_funct_3(X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_funct_1(k7_funct_3(X0,X1))
      & v1_relat_1(k7_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).

fof(f93,plain,
    ( ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f92,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_funct_1(k9_funct_3(X0,X1)) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f41,plain,(
    ! [X0,X1] : v1_funct_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,
    ( ~ v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f91,f57])).

fof(f57,plain,
    ( v1_finset_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f91,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f90,f52])).

fof(f52,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f90,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ v1_finset_1(sK0)
    | ~ v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(superposition,[],[f46,f88])).

fof(f88,plain,(
    k1_relat_1(sK0) = k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f86,f32])).

fof(f86,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).

fof(f59,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f35,f55,f51])).

fof(f35,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f34,f55,f51])).

fof(f34,plain,
    ( v1_finset_1(sK0)
    | v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (22898)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (22898)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f58,f59,f95,f102,f107,f111])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ~spl1_1 | ~spl1_3 | spl1_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    $false | (~spl1_1 | ~spl1_3 | spl1_4)),
% 0.21/0.43    inference(subsumption_resolution,[],[f109,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    v1_finset_1(k1_relat_1(sK0)) | ~spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl1_1 <=> v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    ~v1_finset_1(k1_relat_1(sK0)) | (~spl1_3 | spl1_4)),
% 0.21/0.43    inference(subsumption_resolution,[],[f108,f101])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    v1_finset_1(k2_relat_1(sK0)) | ~spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f99])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl1_3 <=> v1_finset_1(k2_relat_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ~v1_finset_1(k2_relat_1(sK0)) | ~v1_finset_1(k1_relat_1(sK0)) | spl1_4),
% 0.21/0.43    inference(resolution,[],[f106,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0))),
% 0.21/0.43    inference(flattening,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | (~v1_finset_1(X1) | ~v1_finset_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_finset_1(X1) & v1_finset_1(X0)) => v1_finset_1(k2_zfmisc_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ~v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f104])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    spl1_4 <=> v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ~spl1_4 | spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f66,f55,f104])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl1_2 <=> v1_finset_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    v1_finset_1(sK0) | ~v1_finset_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.43    inference(superposition,[],[f44,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.43    inference(resolution,[],[f37,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    (~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))) & (v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ? [X0] : ((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))) & (v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ? [X0] : ((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ? [X0] : (((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0)))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0] : ((v1_finset_1(k1_relat_1(X0)) <~> v1_finset_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0] : ((v1_finset_1(k1_relat_1(X0)) <~> v1_finset_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) <=> v1_finset_1(X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f12])).
% 0.21/0.43  fof(f12,conjecture,(
% 0.21/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) <=> v1_finset_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_finset_1(X1) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    ~spl1_1 | spl1_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f79,f99,f51])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    v1_finset_1(k2_relat_1(sK0)) | ~v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.43    inference(superposition,[],[f78,f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0)),
% 0.21/0.43    inference(resolution,[],[f36,f32])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X0] : (v1_finset_1(k9_relat_1(sK0,X0)) | ~v1_finset_1(X0)) )),
% 0.21/0.43    inference(resolution,[],[f77,f70])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ( ! [X1] : (v1_finset_1(k1_relat_1(k7_relat_1(sK0,X1))) | ~v1_finset_1(X1)) )),
% 0.21/0.43    inference(superposition,[],[f44,f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK0),X0) = k1_relat_1(k7_relat_1(sK0,X0))) )),
% 0.21/0.43    inference(resolution,[],[f42,f32])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_finset_1(k1_relat_1(k7_relat_1(sK0,X0))) | v1_finset_1(k9_relat_1(sK0,X0))) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f76,f32])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0] : (v1_finset_1(k9_relat_1(sK0,X0)) | ~v1_finset_1(k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f75,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    v1_funct_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X0] : (v1_finset_1(k9_relat_1(sK0,X0)) | ~v1_finset_1(k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.43    inference(superposition,[],[f46,f73])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ( ! [X0] : (k9_relat_1(sK0,X0) = k9_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f71,f67])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X0] : (k9_relat_1(sK0,X0) = k9_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))) )),
% 0.21/0.43    inference(resolution,[],[f43,f32])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | (~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_finset_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => v1_finset_1(k9_relat_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    spl1_1 | ~spl1_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    $false | (spl1_1 | ~spl1_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f93,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k9_funct_3(X0,X1))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f40,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k7_funct_3(X0,X1) = k9_funct_3(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k7_funct_3(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_funct_1(k7_funct_3(X0,X1)) & v1_relat_1(k7_funct_3(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ~v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) | (spl1_1 | ~spl1_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f92,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_funct_1(k9_funct_3(X0,X1))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f41,f39])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_funct_1(k7_funct_3(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ~v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) | ~v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) | (spl1_1 | ~spl1_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f91,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    v1_finset_1(sK0) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ~v1_finset_1(sK0) | ~v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) | ~v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_1),
% 0.21/0.43    inference(subsumption_resolution,[],[f90,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ~v1_finset_1(k1_relat_1(sK0)) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    v1_finset_1(k1_relat_1(sK0)) | ~v1_finset_1(sK0) | ~v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) | ~v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.43    inference(superposition,[],[f46,f88])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    k1_relat_1(sK0) = k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f86,f32])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    k1_relat_1(sK0) = k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.43    inference(resolution,[],[f38,f33])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ~spl1_1 | ~spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f55,f51])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl1_1 | spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f34,f55,f51])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (22898)------------------------------
% 0.21/0.43  % (22898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (22898)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (22898)Memory used [KB]: 6140
% 0.21/0.43  % (22898)Time elapsed: 0.028 s
% 0.21/0.43  % (22898)------------------------------
% 0.21/0.43  % (22898)------------------------------
% 0.21/0.44  % (22880)Success in time 0.077 s
%------------------------------------------------------------------------------
