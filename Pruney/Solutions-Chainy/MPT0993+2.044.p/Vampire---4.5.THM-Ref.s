%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :  144 ( 251 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f45,f50,f55,f60,f66,f72,f75])).

fof(f75,plain,
    ( ~ spl4_2
    | ~ spl4_9
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_9
    | spl4_10 ),
    inference(subsumption_resolution,[],[f73,f29])).

fof(f29,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f73,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl4_9
    | spl4_10 ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_9
  <=> ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f71,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_10
  <=> r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f72,plain,
    ( ~ spl4_10
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f67,f53,f22,f69])).

fof(f22,plain,
    ( spl4_1
  <=> r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,
    ( spl4_7
  <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f67,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)
    | spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f24,f54])).

fof(f54,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f24,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f66,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f62,f58,f32,f64])).

fof(f32,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f58,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_relset_1(sK0,sK1,k5_relset_1(sK0,sK1,sK3,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f62,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f61,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl4_8 ),
    inference(superposition,[],[f59,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f59,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k5_relset_1(sK0,sK1,sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f32,f58])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_relset_1(sK0,sK1,k5_relset_1(sK0,sK1,sK3,X0),sK3) )
    | ~ spl4_3 ),
    inference(resolution,[],[f19,f34])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r1_tarski(X1,X2)
      | r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f55,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f51,f48,f32,f53])).

fof(f48,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f51,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f46,f42,f48])).

fof(f42,plain,
    ( spl4_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f46,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f20,f44])).

fof(f44,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f45,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f13,f42])).

fof(f13,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

fof(f35,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f22])).

fof(f17,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (21585)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.41  % (21578)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.41  % (21578)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f76,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f25,f30,f35,f45,f50,f55,f60,f66,f72,f75])).
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    ~spl4_2 | ~spl4_9 | spl4_10),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    $false | (~spl4_2 | ~spl4_9 | spl4_10)),
% 0.21/0.41    inference(subsumption_resolution,[],[f73,f29])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    r1_tarski(sK0,sK2) | ~spl4_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    spl4_2 <=> r1_tarski(sK0,sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    ~r1_tarski(sK0,sK2) | (~spl4_9 | spl4_10)),
% 0.21/0.41    inference(resolution,[],[f71,f65])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    ( ! [X0] : (r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK0,X0)) ) | ~spl4_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f64])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    spl4_9 <=> ! [X0] : (r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK0,X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    ~r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3) | spl4_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f69])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    spl4_10 <=> r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    ~spl4_10 | spl4_1 | ~spl4_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f67,f53,f22,f69])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    spl4_1 <=> r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    spl4_7 <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    ~r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3) | (spl4_1 | ~spl4_7)),
% 0.21/0.41    inference(superposition,[],[f24,f54])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | ~spl4_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f53])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) | spl4_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f22])).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    spl4_9 | ~spl4_3 | ~spl4_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f62,f58,f32,f64])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    spl4_8 <=> ! [X0] : (~r1_tarski(sK0,X0) | r2_relset_1(sK0,sK1,k5_relset_1(sK0,sK1,sK3,X0),sK3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    ( ! [X0] : (r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK0,X0)) ) | (~spl4_3 | ~spl4_8)),
% 0.21/0.41    inference(subsumption_resolution,[],[f61,f34])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f32])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    ( ! [X0] : (r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK0,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_8),
% 0.21/0.41    inference(superposition,[],[f59,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0] : (r2_relset_1(sK0,sK1,k5_relset_1(sK0,sK1,sK3,X0),sK3) | ~r1_tarski(sK0,X0)) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl4_8 | ~spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f56,f32,f58])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_relset_1(sK0,sK1,k5_relset_1(sK0,sK1,sK3,X0),sK3)) ) | ~spl4_3),
% 0.21/0.42    inference(resolution,[],[f19,f34])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(X1,X2) | r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl4_7 | ~spl4_3 | ~spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f51,f48,f32,f53])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl4_6 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | (~spl4_3 | ~spl4_6)),
% 0.21/0.42    inference(resolution,[],[f49,f34])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2)) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl4_6 | ~spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f46,f42,f48])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl4_5 <=> v1_funct_1(sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2)) ) | ~spl4_5),
% 0.21/0.42    inference(resolution,[],[f20,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    v1_funct_1(sK3) | ~spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f42])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    v1_funct_1(sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f27])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    r1_tarski(sK0,sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f22])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (21578)------------------------------
% 0.21/0.42  % (21578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (21578)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (21578)Memory used [KB]: 10618
% 0.21/0.42  % (21578)Time elapsed: 0.006 s
% 0.21/0.42  % (21578)------------------------------
% 0.21/0.42  % (21578)------------------------------
% 0.21/0.42  % (21576)Success in time 0.063 s
%------------------------------------------------------------------------------
