%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 131 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  268 ( 395 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f85,f96,f99,f128,f133,f135])).

fof(f135,plain,
    ( ~ spl6_3
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f75,f132])).

fof(f132,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_8
  <=> ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f75,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f133,plain,
    ( ~ spl6_3
    | spl6_8
    | spl6_7 ),
    inference(avatar_split_clause,[],[f129,f94,f131,f74])).

fof(f94,plain,
    ( spl6_7
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
    | spl6_7 ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f95,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f128,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_6 ),
    inference(avatar_split_clause,[],[f123,f91,f74,f70])).

fof(f70,plain,
    ( spl6_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f91,plain,
    ( spl6_6
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f123,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl6_3
    | spl6_6 ),
    inference(resolution,[],[f119,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f119,plain,
    ( ! [X0] : ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,X0))
    | ~ spl6_3
    | spl6_6 ),
    inference(resolution,[],[f117,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f117,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ spl6_3
    | spl6_6 ),
    inference(resolution,[],[f115,f75])).

fof(f115,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
        | ~ r1_tarski(k1_zfmisc_1(X4),k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) )
    | spl6_6 ),
    inference(resolution,[],[f110,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK3,X0)
        | ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | spl6_6 ),
    inference(resolution,[],[f106,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

% (14562)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f106,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK3,X1)
        | ~ r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) )
    | spl6_6 ),
    inference(resolution,[],[f103,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f103,plain,
    ( ! [X1] : ~ r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | spl6_6 ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,
    ( ! [X0] : ~ r1_tarski(sK3,k2_zfmisc_1(sK2,X0))
    | spl6_6 ),
    inference(resolution,[],[f100,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl6_6 ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f92,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f99,plain,
    ( ~ spl6_3
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl6_3
    | spl6_5 ),
    inference(subsumption_resolution,[],[f75,f97])).

fof(f97,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_5 ),
    inference(resolution,[],[f89,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f96,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_4 ),
    inference(avatar_split_clause,[],[f86,f83,f94,f91,f88])).

fof(f83,plain,
    ( spl6_4
  <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f86,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl6_4 ),
    inference(superposition,[],[f84,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f84,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f80,f66,f83,f74])).

fof(f66,plain,
    ( spl6_1
  <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f80,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_1 ),
    inference(superposition,[],[f67,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f67,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f76,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f72,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f70])).

fof(f42,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f43,f66])).

fof(f43,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (14556)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14555)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (14578)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (14573)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (14563)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (14564)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (14573)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (14556)Refutation not found, incomplete strategy% (14556)------------------------------
% 0.21/0.52  % (14556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14556)Memory used [KB]: 10746
% 0.21/0.52  % (14556)Time elapsed: 0.113 s
% 0.21/0.52  % (14556)------------------------------
% 0.21/0.52  % (14556)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f68,f72,f76,f85,f96,f99,f128,f133,f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~spl6_3 | ~spl6_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    $false | (~spl6_3 | ~spl6_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) ) | ~spl6_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl6_8 <=> ! [X0] : ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~spl6_3 | spl6_8 | spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f94,f131,f74])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl6_7 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) ) | spl6_7),
% 0.21/0.52    inference(resolution,[],[f95,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,sK3,sK3) | spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f94])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ~spl6_2 | ~spl6_3 | spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f123,f91,f74,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl6_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl6_6 <=> v4_relat_1(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2) | (~spl6_3 | spl6_6)),
% 0.21/0.52    inference(resolution,[],[f119,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,X0))) ) | (~spl6_3 | spl6_6)),
% 0.21/0.52    inference(resolution,[],[f117,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | (~spl6_3 | spl6_6)),
% 0.21/0.52    inference(resolution,[],[f115,f75])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(X4)) | ~r1_tarski(k1_zfmisc_1(X4),k1_zfmisc_1(k2_zfmisc_1(sK2,X5)))) ) | spl6_6),
% 0.21/0.52    inference(resolution,[],[f110,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(sK3,X0) | ~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | spl6_6),
% 0.21/0.52    inference(resolution,[],[f106,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  % (14562)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~r2_hidden(sK3,X1) | ~r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))) ) | spl6_6),
% 0.21/0.52    inference(resolution,[],[f103,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | spl6_6),
% 0.21/0.52    inference(resolution,[],[f101,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(sK3,k2_zfmisc_1(sK2,X0))) ) | spl6_6),
% 0.21/0.52    inference(resolution,[],[f100,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl6_6),
% 0.21/0.52    inference(resolution,[],[f92,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~v4_relat_1(sK3,sK2) | spl6_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~spl6_3 | spl6_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    $false | (~spl6_3 | spl6_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_5),
% 0.21/0.52    inference(resolution,[],[f89,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl6_5 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f86,f83,f94,f91,f88])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl6_4 <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,sK3,sK3) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | spl6_4),
% 0.21/0.52    inference(superposition,[],[f84,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | spl6_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ~spl6_3 | ~spl6_4 | spl6_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f80,f66,f83,f74])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl6_1 <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_1),
% 0.21/0.52    inference(superposition,[],[f67,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) | spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f74])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f70])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~spl6_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f66])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14573)------------------------------
% 0.21/0.52  % (14573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14573)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14573)Memory used [KB]: 10746
% 0.21/0.52  % (14573)Time elapsed: 0.105 s
% 0.21/0.52  % (14573)------------------------------
% 0.21/0.52  % (14573)------------------------------
% 0.21/0.52  % (14553)Success in time 0.165 s
%------------------------------------------------------------------------------
