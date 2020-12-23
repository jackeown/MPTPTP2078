%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:53 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 635 expanded)
%              Number of leaves         :   33 ( 200 expanded)
%              Depth                    :   22
%              Number of atoms          :  571 (4110 expanded)
%              Number of equality atoms :   87 ( 175 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26179)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (26178)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f1028,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f132,f151,f164,f787,f800,f813,f846,f889,f992,f1025])).

fof(f1025,plain,
    ( spl4_2
    | ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f1024])).

fof(f1024,plain,
    ( $false
    | spl4_2
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1023,f157])).

fof(f157,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f153,f74])).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f153,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f1023,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1016,f115])).

fof(f115,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1016,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_49 ),
    inference(superposition,[],[f206,f812])).

fof(f812,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f810])).

fof(f810,plain,
    ( spl4_49
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f206,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f100,f170])).

fof(f170,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f77,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f100,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f992,plain,(
    spl4_48 ),
    inference(avatar_contradiction_clause,[],[f991])).

fof(f991,plain,
    ( $false
    | spl4_48 ),
    inference(subsumption_resolution,[],[f990,f157])).

fof(f990,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_48 ),
    inference(subsumption_resolution,[],[f989,f199])).

fof(f199,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f989,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_48 ),
    inference(resolution,[],[f808,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f808,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_48 ),
    inference(avatar_component_clause,[],[f806])).

fof(f806,plain,
    ( spl4_48
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f889,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f888])).

fof(f888,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f866,f181])).

fof(f181,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(superposition,[],[f96,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(resolution,[],[f150,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f150,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_8
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f67,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f866,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f111,f859])).

fof(f859,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4 ),
    inference(resolution,[],[f131,f70])).

fof(f131,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f846,plain,
    ( spl4_3
    | ~ spl4_7
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f845])).

fof(f845,plain,
    ( $false
    | spl4_3
    | ~ spl4_7
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f844,f145])).

fof(f145,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f844,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_3
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f825,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f825,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | spl4_3
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f127,f782])).

fof(f782,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f780])).

fof(f780,plain,
    ( spl4_46
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f127,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_3
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f813,plain,
    ( ~ spl4_48
    | spl4_49 ),
    inference(avatar_split_clause,[],[f804,f810,f806])).

fof(f804,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f803,f98])).

fof(f98,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f69,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f803,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f802,f98])).

fof(f802,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f801,f157])).

fof(f801,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f796,f156])).

fof(f156,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f74])).

fof(f152,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f796,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f213,f790])).

fof(f790,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f767,f789])).

fof(f789,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f755,f257])).

fof(f257,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f90,f95])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f755,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f60,f542])).

fof(f542,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f536,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f536,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f317,f56])).

fof(f317,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f312,f57])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f312,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f92,f59])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f767,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f766,f54])).

fof(f766,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f765,f56])).

fof(f765,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f764,f57])).

fof(f764,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f757,f59])).

fof(f757,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f94,f542])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f213,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f72,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f800,plain,(
    spl4_47 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | spl4_47 ),
    inference(subsumption_resolution,[],[f791,f96])).

fof(f791,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_47 ),
    inference(backward_demodulation,[],[f786,f790])).

fof(f786,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f784])).

fof(f784,plain,
    ( spl4_47
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f787,plain,
    ( spl4_46
    | ~ spl4_47
    | spl4_1 ),
    inference(avatar_split_clause,[],[f778,f109,f784,f780])).

fof(f778,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_1 ),
    inference(subsumption_resolution,[],[f777,f54])).

fof(f777,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f776,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f776,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f775,f56])).

fof(f775,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f774,f57])).

fof(f774,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f773,f58])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f773,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f772,f59])).

fof(f772,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f759,f111])).

fof(f759,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f88,f542])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

% (26169)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f164,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f160,f146])).

fof(f146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f160,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f158,f101])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f75,f62])).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f151,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f142,f148,f144])).

fof(f142,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f119,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f119,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f95,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f132,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f121,f129,f125])).

fof(f121,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f71,f56])).

fof(f116,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f113,f109])).

fof(f61,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:10:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (26160)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (26164)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (26171)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (26152)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (26168)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (26168)Refutation not found, incomplete strategy% (26168)------------------------------
% 0.21/0.55  % (26168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26168)Memory used [KB]: 10746
% 0.21/0.55  % (26168)Time elapsed: 0.128 s
% 0.21/0.55  % (26168)------------------------------
% 0.21/0.55  % (26168)------------------------------
% 0.21/0.55  % (26154)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (26167)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (26155)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (26175)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (26156)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (26157)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (26170)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.58  % (26173)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.58  % (26172)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.69/0.58  % (26162)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.69/0.58  % (26158)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.59  % (26181)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.69/0.59  % (26174)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.69/0.60  % (26180)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.69/0.60  % (26163)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.69/0.60  % (26176)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.69/0.61  % (26161)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.69/0.61  % (26162)Refutation not found, incomplete strategy% (26162)------------------------------
% 1.69/0.61  % (26162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (26162)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (26162)Memory used [KB]: 10874
% 1.69/0.61  % (26162)Time elapsed: 0.189 s
% 1.69/0.61  % (26162)------------------------------
% 1.69/0.61  % (26162)------------------------------
% 1.69/0.61  % (26166)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.91/0.61  % (26165)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.91/0.62  % (26159)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.91/0.62  % (26177)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.91/0.63  % (26180)Refutation not found, incomplete strategy% (26180)------------------------------
% 1.91/0.63  % (26180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.63  % (26180)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.63  
% 1.91/0.63  % (26180)Memory used [KB]: 10874
% 1.91/0.63  % (26180)Time elapsed: 0.202 s
% 1.91/0.63  % (26180)------------------------------
% 1.91/0.63  % (26180)------------------------------
% 1.91/0.64  % (26153)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.91/0.65  % (26158)Refutation found. Thanks to Tanya!
% 1.91/0.65  % SZS status Theorem for theBenchmark
% 1.91/0.65  % SZS output start Proof for theBenchmark
% 1.91/0.65  % (26179)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.91/0.65  % (26178)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.33/0.67  fof(f1028,plain,(
% 2.33/0.67    $false),
% 2.33/0.67    inference(avatar_sat_refutation,[],[f116,f132,f151,f164,f787,f800,f813,f846,f889,f992,f1025])).
% 2.33/0.67  fof(f1025,plain,(
% 2.33/0.67    spl4_2 | ~spl4_49),
% 2.33/0.67    inference(avatar_contradiction_clause,[],[f1024])).
% 2.33/0.67  fof(f1024,plain,(
% 2.33/0.67    $false | (spl4_2 | ~spl4_49)),
% 2.33/0.67    inference(subsumption_resolution,[],[f1023,f157])).
% 2.33/0.67  fof(f157,plain,(
% 2.33/0.67    v1_relat_1(sK3)),
% 2.33/0.67    inference(subsumption_resolution,[],[f153,f74])).
% 2.33/0.67  fof(f74,plain,(
% 2.33/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.33/0.67    inference(cnf_transformation,[],[f10])).
% 2.33/0.67  fof(f10,axiom,(
% 2.33/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.33/0.67  fof(f153,plain,(
% 2.33/0.67    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.33/0.67    inference(resolution,[],[f73,f59])).
% 2.33/0.67  fof(f59,plain,(
% 2.33/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  fof(f46,plain,(
% 2.33/0.67    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.33/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).
% 2.33/0.67  fof(f44,plain,(
% 2.33/0.67    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.33/0.67    introduced(choice_axiom,[])).
% 2.33/0.67  fof(f45,plain,(
% 2.33/0.67    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.33/0.67    introduced(choice_axiom,[])).
% 2.33/0.67  fof(f25,plain,(
% 2.33/0.67    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.33/0.67    inference(flattening,[],[f24])).
% 2.33/0.67  fof(f24,plain,(
% 2.33/0.67    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.33/0.67    inference(ennf_transformation,[],[f23])).
% 2.33/0.67  fof(f23,negated_conjecture,(
% 2.33/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.33/0.67    inference(negated_conjecture,[],[f22])).
% 2.33/0.67  fof(f22,conjecture,(
% 2.33/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 2.33/0.67  fof(f73,plain,(
% 2.33/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f29])).
% 2.33/0.67  fof(f29,plain,(
% 2.33/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.33/0.67    inference(ennf_transformation,[],[f8])).
% 2.33/0.67  fof(f8,axiom,(
% 2.33/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.33/0.67  fof(f1023,plain,(
% 2.33/0.67    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_49)),
% 2.33/0.67    inference(subsumption_resolution,[],[f1016,f115])).
% 2.33/0.67  fof(f115,plain,(
% 2.33/0.67    ~v2_funct_2(sK3,sK0) | spl4_2),
% 2.33/0.67    inference(avatar_component_clause,[],[f113])).
% 2.33/0.67  fof(f113,plain,(
% 2.33/0.67    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.33/0.67  fof(f1016,plain,(
% 2.33/0.67    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_49),
% 2.33/0.67    inference(superposition,[],[f206,f812])).
% 2.33/0.67  fof(f812,plain,(
% 2.33/0.67    sK0 = k2_relat_1(sK3) | ~spl4_49),
% 2.33/0.67    inference(avatar_component_clause,[],[f810])).
% 2.33/0.67  fof(f810,plain,(
% 2.33/0.67    spl4_49 <=> sK0 = k2_relat_1(sK3)),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.33/0.67  fof(f206,plain,(
% 2.33/0.67    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.33/0.67    inference(subsumption_resolution,[],[f100,f170])).
% 2.33/0.67  fof(f170,plain,(
% 2.33/0.67    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.33/0.67    inference(resolution,[],[f77,f101])).
% 2.33/0.67  fof(f101,plain,(
% 2.33/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.33/0.67    inference(equality_resolution,[],[f81])).
% 2.33/0.67  fof(f81,plain,(
% 2.33/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.33/0.67    inference(cnf_transformation,[],[f50])).
% 2.33/0.67  fof(f50,plain,(
% 2.33/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.67    inference(flattening,[],[f49])).
% 2.33/0.67  fof(f49,plain,(
% 2.33/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.67    inference(nnf_transformation,[],[f2])).
% 2.33/0.67  fof(f2,axiom,(
% 2.33/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.33/0.67  fof(f77,plain,(
% 2.33/0.67    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f47])).
% 2.33/0.67  fof(f47,plain,(
% 2.33/0.67    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.33/0.67    inference(nnf_transformation,[],[f32])).
% 2.33/0.67  fof(f32,plain,(
% 2.33/0.67    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.33/0.67    inference(ennf_transformation,[],[f9])).
% 2.33/0.67  fof(f9,axiom,(
% 2.33/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.33/0.67  fof(f100,plain,(
% 2.33/0.67    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.33/0.67    inference(equality_resolution,[],[f79])).
% 2.33/0.67  fof(f79,plain,(
% 2.33/0.67    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f48])).
% 2.33/0.67  fof(f48,plain,(
% 2.33/0.67    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.33/0.67    inference(nnf_transformation,[],[f34])).
% 2.33/0.67  fof(f34,plain,(
% 2.33/0.67    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.33/0.67    inference(flattening,[],[f33])).
% 2.33/0.67  fof(f33,plain,(
% 2.33/0.67    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.33/0.67    inference(ennf_transformation,[],[f17])).
% 2.33/0.67  fof(f17,axiom,(
% 2.33/0.67    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 2.33/0.67  fof(f992,plain,(
% 2.33/0.67    spl4_48),
% 2.33/0.67    inference(avatar_contradiction_clause,[],[f991])).
% 2.33/0.67  fof(f991,plain,(
% 2.33/0.67    $false | spl4_48),
% 2.33/0.67    inference(subsumption_resolution,[],[f990,f157])).
% 2.33/0.67  fof(f990,plain,(
% 2.33/0.67    ~v1_relat_1(sK3) | spl4_48),
% 2.33/0.67    inference(subsumption_resolution,[],[f989,f199])).
% 2.33/0.67  fof(f199,plain,(
% 2.33/0.67    v5_relat_1(sK3,sK0)),
% 2.33/0.67    inference(resolution,[],[f87,f59])).
% 2.33/0.67  fof(f87,plain,(
% 2.33/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f35])).
% 2.33/0.67  fof(f35,plain,(
% 2.33/0.67    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.67    inference(ennf_transformation,[],[f14])).
% 2.33/0.67  fof(f14,axiom,(
% 2.33/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.33/0.67  fof(f989,plain,(
% 2.33/0.67    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_48),
% 2.33/0.67    inference(resolution,[],[f808,f76])).
% 2.33/0.67  fof(f76,plain,(
% 2.33/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f47])).
% 2.33/0.67  fof(f808,plain,(
% 2.33/0.67    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_48),
% 2.33/0.67    inference(avatar_component_clause,[],[f806])).
% 2.33/0.67  fof(f806,plain,(
% 2.33/0.67    spl4_48 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.33/0.67  fof(f889,plain,(
% 2.33/0.67    spl4_1 | ~spl4_4 | ~spl4_8),
% 2.33/0.67    inference(avatar_contradiction_clause,[],[f888])).
% 2.33/0.67  fof(f888,plain,(
% 2.33/0.67    $false | (spl4_1 | ~spl4_4 | ~spl4_8)),
% 2.33/0.67    inference(subsumption_resolution,[],[f866,f181])).
% 2.33/0.67  fof(f181,plain,(
% 2.33/0.67    v2_funct_1(k1_xboole_0) | ~spl4_8),
% 2.33/0.67    inference(superposition,[],[f96,f169])).
% 2.33/0.67  fof(f169,plain,(
% 2.33/0.67    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_8),
% 2.33/0.67    inference(resolution,[],[f150,f70])).
% 2.33/0.67  fof(f70,plain,(
% 2.33/0.67    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.33/0.67    inference(cnf_transformation,[],[f26])).
% 2.33/0.67  fof(f26,plain,(
% 2.33/0.67    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.33/0.67    inference(ennf_transformation,[],[f1])).
% 2.33/0.67  fof(f1,axiom,(
% 2.33/0.67    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.33/0.67  fof(f150,plain,(
% 2.33/0.67    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl4_8),
% 2.33/0.67    inference(avatar_component_clause,[],[f148])).
% 2.33/0.67  fof(f148,plain,(
% 2.33/0.67    spl4_8 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.33/0.67  fof(f96,plain,(
% 2.33/0.67    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.33/0.67    inference(definition_unfolding,[],[f67,f64])).
% 2.33/0.67  fof(f64,plain,(
% 2.33/0.67    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f20])).
% 2.33/0.67  fof(f20,axiom,(
% 2.33/0.67    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.33/0.67  fof(f67,plain,(
% 2.33/0.67    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.33/0.67    inference(cnf_transformation,[],[f13])).
% 2.33/0.67  fof(f13,axiom,(
% 2.33/0.67    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.33/0.67  fof(f866,plain,(
% 2.33/0.67    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_4)),
% 2.33/0.67    inference(backward_demodulation,[],[f111,f859])).
% 2.33/0.67  fof(f859,plain,(
% 2.33/0.67    k1_xboole_0 = sK2 | ~spl4_4),
% 2.33/0.67    inference(resolution,[],[f131,f70])).
% 2.33/0.67  fof(f131,plain,(
% 2.33/0.67    v1_xboole_0(sK2) | ~spl4_4),
% 2.33/0.67    inference(avatar_component_clause,[],[f129])).
% 2.33/0.67  fof(f129,plain,(
% 2.33/0.67    spl4_4 <=> v1_xboole_0(sK2)),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.33/0.67  fof(f111,plain,(
% 2.33/0.67    ~v2_funct_1(sK2) | spl4_1),
% 2.33/0.67    inference(avatar_component_clause,[],[f109])).
% 2.33/0.67  fof(f109,plain,(
% 2.33/0.67    spl4_1 <=> v2_funct_1(sK2)),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.33/0.67  fof(f846,plain,(
% 2.33/0.67    spl4_3 | ~spl4_7 | ~spl4_46),
% 2.33/0.67    inference(avatar_contradiction_clause,[],[f845])).
% 2.33/0.67  fof(f845,plain,(
% 2.33/0.67    $false | (spl4_3 | ~spl4_7 | ~spl4_46)),
% 2.33/0.67    inference(subsumption_resolution,[],[f844,f145])).
% 2.33/0.67  fof(f145,plain,(
% 2.33/0.67    v1_xboole_0(k1_xboole_0) | ~spl4_7),
% 2.33/0.67    inference(avatar_component_clause,[],[f144])).
% 2.33/0.67  fof(f144,plain,(
% 2.33/0.67    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.33/0.67  fof(f844,plain,(
% 2.33/0.67    ~v1_xboole_0(k1_xboole_0) | (spl4_3 | ~spl4_46)),
% 2.33/0.67    inference(forward_demodulation,[],[f825,f104])).
% 2.33/0.67  fof(f104,plain,(
% 2.33/0.67    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.33/0.67    inference(equality_resolution,[],[f84])).
% 2.33/0.67  fof(f84,plain,(
% 2.33/0.67    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.33/0.67    inference(cnf_transformation,[],[f52])).
% 2.33/0.67  fof(f52,plain,(
% 2.33/0.67    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/0.67    inference(flattening,[],[f51])).
% 2.33/0.67  fof(f51,plain,(
% 2.33/0.67    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/0.67    inference(nnf_transformation,[],[f6])).
% 2.33/0.67  fof(f6,axiom,(
% 2.33/0.67    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.33/0.67  fof(f825,plain,(
% 2.33/0.67    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (spl4_3 | ~spl4_46)),
% 2.33/0.67    inference(backward_demodulation,[],[f127,f782])).
% 2.33/0.67  fof(f782,plain,(
% 2.33/0.67    k1_xboole_0 = sK0 | ~spl4_46),
% 2.33/0.67    inference(avatar_component_clause,[],[f780])).
% 2.33/0.67  fof(f780,plain,(
% 2.33/0.67    spl4_46 <=> k1_xboole_0 = sK0),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.33/0.67  fof(f127,plain,(
% 2.33/0.67    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_3),
% 2.33/0.67    inference(avatar_component_clause,[],[f125])).
% 2.33/0.67  fof(f125,plain,(
% 2.33/0.67    spl4_3 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.33/0.67  fof(f813,plain,(
% 2.33/0.67    ~spl4_48 | spl4_49),
% 2.33/0.67    inference(avatar_split_clause,[],[f804,f810,f806])).
% 2.33/0.67  fof(f804,plain,(
% 2.33/0.67    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0)),
% 2.33/0.67    inference(forward_demodulation,[],[f803,f98])).
% 2.33/0.67  fof(f98,plain,(
% 2.33/0.67    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.33/0.67    inference(definition_unfolding,[],[f69,f64])).
% 2.33/0.67  fof(f69,plain,(
% 2.33/0.67    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.33/0.67    inference(cnf_transformation,[],[f12])).
% 2.33/0.67  fof(f12,axiom,(
% 2.33/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.33/0.67  fof(f803,plain,(
% 2.33/0.67    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 2.33/0.67    inference(forward_demodulation,[],[f802,f98])).
% 2.33/0.67  fof(f802,plain,(
% 2.33/0.67    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 2.33/0.67    inference(subsumption_resolution,[],[f801,f157])).
% 2.33/0.67  fof(f801,plain,(
% 2.33/0.67    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 2.33/0.67    inference(subsumption_resolution,[],[f796,f156])).
% 2.33/0.67  fof(f156,plain,(
% 2.33/0.67    v1_relat_1(sK2)),
% 2.33/0.67    inference(subsumption_resolution,[],[f152,f74])).
% 2.33/0.67  fof(f152,plain,(
% 2.33/0.67    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.33/0.67    inference(resolution,[],[f73,f56])).
% 2.33/0.67  fof(f56,plain,(
% 2.33/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  fof(f796,plain,(
% 2.33/0.67    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 2.33/0.67    inference(superposition,[],[f213,f790])).
% 2.33/0.67  fof(f790,plain,(
% 2.33/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.33/0.67    inference(global_subsumption,[],[f767,f789])).
% 2.33/0.67  fof(f789,plain,(
% 2.33/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.33/0.67    inference(resolution,[],[f755,f257])).
% 2.33/0.67  fof(f257,plain,(
% 2.33/0.67    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.33/0.67    inference(resolution,[],[f90,f95])).
% 2.33/0.67  fof(f95,plain,(
% 2.33/0.67    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.33/0.67    inference(definition_unfolding,[],[f65,f64])).
% 2.33/0.67  fof(f65,plain,(
% 2.33/0.67    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.33/0.67    inference(cnf_transformation,[],[f16])).
% 2.33/0.67  fof(f16,axiom,(
% 2.33/0.67    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.33/0.67  fof(f90,plain,(
% 2.33/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.67    inference(cnf_transformation,[],[f53])).
% 2.33/0.67  fof(f53,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.67    inference(nnf_transformation,[],[f39])).
% 2.33/0.67  fof(f39,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.67    inference(flattening,[],[f38])).
% 2.33/0.67  fof(f38,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.33/0.67    inference(ennf_transformation,[],[f15])).
% 2.33/0.67  fof(f15,axiom,(
% 2.33/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.33/0.67  fof(f755,plain,(
% 2.33/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.33/0.67    inference(backward_demodulation,[],[f60,f542])).
% 2.33/0.67  fof(f542,plain,(
% 2.33/0.67    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.33/0.67    inference(subsumption_resolution,[],[f536,f54])).
% 2.33/0.67  fof(f54,plain,(
% 2.33/0.67    v1_funct_1(sK2)),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  fof(f536,plain,(
% 2.33/0.67    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.33/0.67    inference(resolution,[],[f317,f56])).
% 2.33/0.67  fof(f317,plain,(
% 2.33/0.67    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 2.33/0.67    inference(subsumption_resolution,[],[f312,f57])).
% 2.33/0.67  fof(f57,plain,(
% 2.33/0.67    v1_funct_1(sK3)),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  fof(f312,plain,(
% 2.33/0.67    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 2.33/0.67    inference(resolution,[],[f92,f59])).
% 2.33/0.67  fof(f92,plain,(
% 2.33/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f41])).
% 2.33/0.67  fof(f41,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.33/0.67    inference(flattening,[],[f40])).
% 2.33/0.67  fof(f40,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.33/0.67    inference(ennf_transformation,[],[f19])).
% 2.33/0.67  fof(f19,axiom,(
% 2.33/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.33/0.67  fof(f60,plain,(
% 2.33/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  fof(f767,plain,(
% 2.33/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.33/0.67    inference(subsumption_resolution,[],[f766,f54])).
% 2.33/0.67  fof(f766,plain,(
% 2.33/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.33/0.67    inference(subsumption_resolution,[],[f765,f56])).
% 2.33/0.67  fof(f765,plain,(
% 2.33/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.33/0.67    inference(subsumption_resolution,[],[f764,f57])).
% 2.33/0.67  fof(f764,plain,(
% 2.33/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.33/0.67    inference(subsumption_resolution,[],[f757,f59])).
% 2.33/0.67  fof(f757,plain,(
% 2.33/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.33/0.67    inference(superposition,[],[f94,f542])).
% 2.33/0.67  fof(f94,plain,(
% 2.33/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f43])).
% 2.33/0.67  fof(f43,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.33/0.67    inference(flattening,[],[f42])).
% 2.33/0.67  fof(f42,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.33/0.67    inference(ennf_transformation,[],[f18])).
% 2.33/0.67  fof(f18,axiom,(
% 2.33/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.33/0.67  fof(f213,plain,(
% 2.33/0.67    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 2.33/0.67    inference(resolution,[],[f72,f82])).
% 2.33/0.67  fof(f82,plain,(
% 2.33/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f50])).
% 2.33/0.67  fof(f72,plain,(
% 2.33/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f28])).
% 2.33/0.67  fof(f28,plain,(
% 2.33/0.67    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.33/0.67    inference(ennf_transformation,[],[f11])).
% 2.33/0.67  fof(f11,axiom,(
% 2.33/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 2.33/0.67  fof(f800,plain,(
% 2.33/0.67    spl4_47),
% 2.33/0.67    inference(avatar_contradiction_clause,[],[f799])).
% 2.33/0.67  fof(f799,plain,(
% 2.33/0.67    $false | spl4_47),
% 2.33/0.67    inference(subsumption_resolution,[],[f791,f96])).
% 2.33/0.67  fof(f791,plain,(
% 2.33/0.67    ~v2_funct_1(k6_partfun1(sK0)) | spl4_47),
% 2.33/0.67    inference(backward_demodulation,[],[f786,f790])).
% 2.33/0.67  fof(f786,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_47),
% 2.33/0.67    inference(avatar_component_clause,[],[f784])).
% 2.33/0.67  fof(f784,plain,(
% 2.33/0.67    spl4_47 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 2.33/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 2.33/0.67  fof(f787,plain,(
% 2.33/0.67    spl4_46 | ~spl4_47 | spl4_1),
% 2.33/0.67    inference(avatar_split_clause,[],[f778,f109,f784,f780])).
% 2.33/0.67  fof(f778,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | spl4_1),
% 2.33/0.67    inference(subsumption_resolution,[],[f777,f54])).
% 2.33/0.67  fof(f777,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | spl4_1),
% 2.33/0.67    inference(subsumption_resolution,[],[f776,f55])).
% 2.33/0.67  fof(f55,plain,(
% 2.33/0.67    v1_funct_2(sK2,sK0,sK1)),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  fof(f776,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 2.33/0.67    inference(subsumption_resolution,[],[f775,f56])).
% 2.33/0.67  fof(f775,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 2.33/0.67    inference(subsumption_resolution,[],[f774,f57])).
% 2.33/0.67  fof(f774,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 2.33/0.67    inference(subsumption_resolution,[],[f773,f58])).
% 2.33/0.67  fof(f58,plain,(
% 2.33/0.67    v1_funct_2(sK3,sK1,sK0)),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  fof(f773,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 2.33/0.67    inference(subsumption_resolution,[],[f772,f59])).
% 2.33/0.67  fof(f772,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 2.33/0.67    inference(subsumption_resolution,[],[f759,f111])).
% 2.33/0.67  fof(f759,plain,(
% 2.33/0.67    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 2.33/0.67    inference(superposition,[],[f88,f542])).
% 2.33/0.67  fof(f88,plain,(
% 2.33/0.67    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f37])).
% 2.33/0.67  fof(f37,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.33/0.67    inference(flattening,[],[f36])).
% 2.33/0.67  % (26169)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.33/0.67  fof(f36,plain,(
% 2.33/0.67    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.33/0.67    inference(ennf_transformation,[],[f21])).
% 2.33/0.67  fof(f21,axiom,(
% 2.33/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 2.33/0.67  fof(f164,plain,(
% 2.33/0.67    spl4_7),
% 2.33/0.67    inference(avatar_contradiction_clause,[],[f163])).
% 2.33/0.67  fof(f163,plain,(
% 2.33/0.67    $false | spl4_7),
% 2.33/0.67    inference(subsumption_resolution,[],[f160,f146])).
% 2.33/0.67  fof(f146,plain,(
% 2.33/0.67    ~v1_xboole_0(k1_xboole_0) | spl4_7),
% 2.33/0.67    inference(avatar_component_clause,[],[f144])).
% 2.33/0.67  fof(f160,plain,(
% 2.33/0.67    v1_xboole_0(k1_xboole_0)),
% 2.33/0.67    inference(resolution,[],[f158,f101])).
% 2.33/0.67  fof(f158,plain,(
% 2.33/0.67    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 2.33/0.67    inference(resolution,[],[f75,f62])).
% 2.33/0.67  fof(f62,plain,(
% 2.33/0.67    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f4])).
% 2.33/0.67  fof(f4,axiom,(
% 2.33/0.67    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.33/0.67  fof(f75,plain,(
% 2.33/0.67    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f31])).
% 2.33/0.67  fof(f31,plain,(
% 2.33/0.67    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.33/0.67    inference(flattening,[],[f30])).
% 2.33/0.67  fof(f30,plain,(
% 2.33/0.67    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.33/0.67    inference(ennf_transformation,[],[f5])).
% 2.33/0.67  fof(f5,axiom,(
% 2.33/0.67    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.33/0.67  fof(f151,plain,(
% 2.33/0.67    ~spl4_7 | spl4_8),
% 2.33/0.67    inference(avatar_split_clause,[],[f142,f148,f144])).
% 2.33/0.67  fof(f142,plain,(
% 2.33/0.67    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 2.33/0.67    inference(resolution,[],[f119,f71])).
% 2.33/0.67  fof(f71,plain,(
% 2.33/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.33/0.67    inference(cnf_transformation,[],[f27])).
% 2.33/0.67  fof(f27,plain,(
% 2.33/0.67    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.33/0.67    inference(ennf_transformation,[],[f7])).
% 2.33/0.67  fof(f7,axiom,(
% 2.33/0.67    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.33/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 2.33/0.67  fof(f119,plain,(
% 2.33/0.67    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 2.33/0.67    inference(superposition,[],[f95,f103])).
% 2.33/0.67  fof(f103,plain,(
% 2.33/0.67    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.33/0.67    inference(equality_resolution,[],[f85])).
% 2.33/0.67  fof(f85,plain,(
% 2.33/0.67    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.33/0.67    inference(cnf_transformation,[],[f52])).
% 2.33/0.67  fof(f132,plain,(
% 2.33/0.67    ~spl4_3 | spl4_4),
% 2.33/0.67    inference(avatar_split_clause,[],[f121,f129,f125])).
% 2.33/0.67  fof(f121,plain,(
% 2.33/0.67    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 2.33/0.67    inference(resolution,[],[f71,f56])).
% 2.33/0.67  fof(f116,plain,(
% 2.33/0.67    ~spl4_1 | ~spl4_2),
% 2.33/0.67    inference(avatar_split_clause,[],[f61,f113,f109])).
% 2.33/0.67  fof(f61,plain,(
% 2.33/0.67    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.33/0.67    inference(cnf_transformation,[],[f46])).
% 2.33/0.67  % SZS output end Proof for theBenchmark
% 2.33/0.67  % (26158)------------------------------
% 2.33/0.67  % (26158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.67  % (26158)Termination reason: Refutation
% 2.33/0.67  
% 2.33/0.67  % (26158)Memory used [KB]: 11385
% 2.33/0.67  % (26158)Time elapsed: 0.210 s
% 2.33/0.67  % (26158)------------------------------
% 2.33/0.67  % (26158)------------------------------
% 2.33/0.67  % (26151)Success in time 0.31 s
%------------------------------------------------------------------------------
