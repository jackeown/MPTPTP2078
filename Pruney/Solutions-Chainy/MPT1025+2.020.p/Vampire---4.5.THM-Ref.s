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
% DateTime   : Thu Dec  3 13:06:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 161 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  274 ( 479 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f61,f66,f77,f87,f104,f117,f134,f139,f157,f163,f177,f183])).

fof(f183,plain,
    ( ~ spl6_10
    | ~ spl6_15
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_15
    | spl6_18 ),
    inference(subsumption_resolution,[],[f181,f156])).

fof(f156,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_15
  <=> r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f181,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl6_10
    | spl6_18 ),
    inference(resolution,[],[f176,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f116,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f116,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_10
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f176,plain,
    ( ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_18
  <=> m1_subset_1(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f177,plain,
    ( ~ spl6_18
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f167,f160,f131,f174])).

fof(f131,plain,
    ( spl6_12
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f160,plain,
    ( spl6_16
  <=> sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f167,plain,
    ( ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f166,f133])).

fof(f133,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f166,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_16 ),
    inference(superposition,[],[f22,f162])).

fof(f162,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f22,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f163,plain,
    ( spl6_16
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f141,f136,f74,f45,f160])).

fof(f45,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f74,plain,
    ( spl6_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f136,plain,
    ( spl6_13
  <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f141,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(resolution,[],[f138,f106])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK3,X2) = X3 )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f50,f76])).

fof(f76,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f50,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f47,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f47,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f138,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f157,plain,
    ( spl6_15
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f142,f136,f74,f45,f154])).

fof(f142,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(resolution,[],[f138,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f49,f76])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | r2_hidden(X0,k1_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,
    ( spl6_13
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f121,f101,f74,f136])).

fof(f101,plain,
    ( spl6_9
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f121,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f78,f103])).

fof(f103,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(k4_tarski(sK5(X0,X1,sK3),X0),sK3) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

% (12496)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (12494)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (12486)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f134,plain,
    ( spl6_12
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f118,f101,f74,f131])).

fof(f118,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f79,f103])).

fof(f79,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X3))
        | r2_hidden(sK5(X2,X3,sK3),X3) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f117,plain,
    ( spl6_10
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f109,f84,f74,f114])).

fof(f84,plain,
    ( spl6_6
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f109,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f107,f86])).

fof(f86,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f82,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,
    ( ! [X8] :
        ( r1_tarski(k1_relat_1(sK3),X8)
        | ~ v4_relat_1(sK3,X8) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f104,plain,
    ( spl6_9
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f99,f63,f58,f101])).

fof(f58,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f63,plain,
    ( spl6_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f99,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(superposition,[],[f65,f67])).

fof(f67,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f65,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f87,plain,
    ( spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f68,f58,f84])).

fof(f68,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f77,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f70,f58,f74])).

fof(f70,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f66,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:50:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (12487)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12487)Refutation not found, incomplete strategy% (12487)------------------------------
% 0.21/0.50  % (12487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12487)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12487)Memory used [KB]: 10618
% 0.21/0.50  % (12487)Time elapsed: 0.070 s
% 0.21/0.50  % (12487)------------------------------
% 0.21/0.50  % (12487)------------------------------
% 0.21/0.50  % (12499)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12489)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (12488)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (12489)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f48,f61,f66,f77,f87,f104,f117,f134,f139,f157,f163,f177,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~spl6_10 | ~spl6_15 | spl6_18),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    $false | (~spl6_10 | ~spl6_15 | spl6_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f181,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl6_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl6_15 <=> r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ~r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl6_10 | spl6_18)),
% 0.21/0.51    inference(resolution,[],[f176,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(X0,sK0) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl6_10),
% 0.21/0.51    inference(resolution,[],[f116,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) | ~spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl6_10 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl6_18 <=> m1_subset_1(sK5(sK4,sK2,sK3),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~spl6_18 | ~spl6_12 | ~spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f167,f160,f131,f174])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl6_12 <=> r2_hidden(sK5(sK4,sK2,sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl6_16 <=> sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | (~spl6_12 | ~spl6_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~spl6_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | ~spl6_16),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    sK4 != sK4 | ~r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK5(sK4,sK2,sK3),sK0) | ~spl6_16),
% 0.21/0.51    inference(superposition,[],[f22,f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~spl6_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl6_16 | ~spl6_1 | ~spl6_5 | ~spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f141,f136,f74,f45,f160])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    spl6_1 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl6_5 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl6_13 <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | (~spl6_1 | ~spl6_5 | ~spl6_13)),
% 0.21/0.51    inference(resolution,[],[f138,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK3,X2) = X3) ) | (~spl6_1 | ~spl6_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f50,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | ~spl6_1),
% 0.21/0.51    inference(resolution,[],[f47,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f45])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl6_15 | ~spl6_1 | ~spl6_5 | ~spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f142,f136,f74,f45,f154])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl6_1 | ~spl6_5 | ~spl6_13)),
% 0.21/0.51    inference(resolution,[],[f138,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,k1_relat_1(sK3))) ) | (~spl6_1 | ~spl6_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f49,f76])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(sK3) | r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(k4_tarski(X0,X1),sK3)) ) | ~spl6_1),
% 0.21/0.51    inference(resolution,[],[f47,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl6_13 | ~spl6_5 | ~spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f121,f101,f74,f136])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl6_9 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | (~spl6_5 | ~spl6_9)),
% 0.21/0.51    inference(resolution,[],[f78,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,sK3),X0),sK3)) ) | ~spl6_5),
% 0.21/0.51    inference(resolution,[],[f76,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.51  % (12496)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (12494)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (12486)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl6_12 | ~spl6_5 | ~spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f118,f101,f74,f131])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    r2_hidden(sK5(sK4,sK2,sK3),sK2) | (~spl6_5 | ~spl6_9)),
% 0.21/0.51    inference(resolution,[],[f79,f103])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(X2,k9_relat_1(sK3,X3)) | r2_hidden(sK5(X2,X3,sK3),X3)) ) | ~spl6_5),
% 0.21/0.51    inference(resolution,[],[f76,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl6_10 | ~spl6_5 | ~spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f109,f84,f74,f114])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl6_6 <=> v4_relat_1(sK3,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) | (~spl6_5 | ~spl6_6)),
% 0.21/0.51    inference(resolution,[],[f107,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    v4_relat_1(sK3,sK0) | ~spl6_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0] : (~v4_relat_1(sK3,X0) | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))) ) | ~spl6_5),
% 0.21/0.51    inference(resolution,[],[f82,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X8] : (r1_tarski(k1_relat_1(sK3),X8) | ~v4_relat_1(sK3,X8)) ) | ~spl6_5),
% 0.21/0.51    inference(resolution,[],[f76,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl6_9 | ~spl6_3 | ~spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f99,f63,f58,f101])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl6_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_3 | ~spl6_4)),
% 0.21/0.51    inference(superposition,[],[f65,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f60,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f63])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl6_6 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f58,f84])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    v4_relat_1(sK3,sK0) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f60,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl6_5 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f58,f74])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f60,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f63])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f58])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f45])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12489)------------------------------
% 0.21/0.51  % (12489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12489)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12489)Memory used [KB]: 10746
% 0.21/0.51  % (12489)Time elapsed: 0.082 s
% 0.21/0.51  % (12489)------------------------------
% 0.21/0.51  % (12489)------------------------------
% 0.21/0.52  % (12485)Success in time 0.154 s
%------------------------------------------------------------------------------
